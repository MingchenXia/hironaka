"""Draft-only immutable Release Sink. Importing performs no I/O.

No production CLI is provided. Construct with an explicitly supplied GhClient.
Tests supply in-memory clients or a local fake gh executable, never real gh.
"""
from __future__ import annotations
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import tempfile
import time
from urllib.parse import quote

BLOCK = 65536
MAX_PART = 256 * 1024 * 1024
MAX_MANIFEST = 64 * 1024 * 1024


class SinkError(RuntimeError):
    pass


class Conflict(SinkError):
    pass


class DraftRequired(SinkError):
    pass


class UncertainMutation(SinkError):
    pass


class GhFailure(SinkError):
    def __init__(self, code, stderr=b''):
        super().__init__(f'gh operation failed (exit {code})')
        self.code, self.stderr = code, stderr[:4096]


class ProcessReader(io.RawIOBase):
    """Streaming subprocess with bounded stdout, bounded retained stderr, timeout.

    Both pipes are drained together. Context close also reaps an unread child.
    No full binary asset is captured by the adapter's hash/readback operations.
    """
    def __init__(self, argv, *, env, limit, timeout, input_bytes=None):
        super().__init__()
        self.process = None
        self.selector = None
        if limit < 0 or not math.isfinite(timeout) or timeout <= 0:
            raise ValueError('Invalid process limits')
        if input_bytes is not None and len(input_bytes) > 4096:
            raise ValueError('Process stdin metadata exceeds bound')
        self.limit, self.total = limit, 0
        self.deadline = time.monotonic() + timeout
        self.stderr = bytearray()
        self.done = False
        self.process = subprocess.Popen(argv, stdin=subprocess.PIPE if input_bytes is not None else subprocess.DEVNULL,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                        env=env, start_new_session=True)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.process.stdout, selectors.EVENT_READ, 'out')
        self.selector.register(self.process.stderr, selectors.EVENT_READ, 'err')
        try:
            if input_bytes is not None:
                self.process.stdin.write(input_bytes)
                self.process.stdin.close()
        except BaseException:
            self.close()
            raise

    def readable(self):
        return True

    def read(self, size=-1):
        if self.closed:
            raise ValueError('Read of closed stream')
        if size == 0 or self.done:
            return b''
        data = bytearray()
        try:
            while not self.done and (size < 0 or len(data) < size):
                remaining = self.deadline - time.monotonic()
                if remaining <= 0:
                    raise SinkError('gh operation timed out')
                events = self.selector.select(min(remaining, .2))
                for key, _ in events:
                    want = BLOCK if key.data == 'err' or size < 0 else min(BLOCK, size-len(data))
                    chunk = os.read(key.fileobj.fileno(), want)
                    if not chunk:
                        self.selector.unregister(key.fileobj)
                    elif key.data == 'err':
                        self.stderr.extend(chunk[:max(0, 4096-len(self.stderr))])
                    else:
                        self.total += len(chunk)
                        if self.total > self.limit:
                            raise SinkError('gh stdout exceeded its declared bound')
                        data.extend(chunk)
                if not self.selector.get_map():
                    code = self.process.wait(timeout=max(.001, self.deadline-time.monotonic()))
                    self.done = True
                    if code:
                        raise GhFailure(code, bytes(self.stderr))
            return bytes(data)
        except BaseException:
            self.close()
            raise

    def close(self):
        if not self.closed:
            if self.process is not None:
                # Also clean up owned descendants if the main process already exited.
                try:
                    os.killpg(self.process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                self.process.wait()
                for pipe in (self.process.stdin, self.process.stdout, self.process.stderr):
                    if pipe is not None:
                        pipe.close()
            if self.selector is not None:
                self.selector.close()
        super().close()


class GhRunner:
    """Transport implementation; tests invoke only an explicit local fake binary."""
    def __init__(self, executable='gh', *, env=None, timeout=300, json_limit=2*1024*1024):
        self.executable, self.timeout, self.json_limit = executable, timeout, json_limit
        self.env = dict(os.environ if env is None else env)
        self.env.pop('GH_DEBUG', None)
        self.env.update(GH_PROMPT_DISABLED='1', GH_NO_UPDATE_NOTIFIER='1', NO_COLOR='1')

    def open(self, args, *, limit, input_bytes=None):
        return ProcessReader([self.executable, *args], env=self.env, limit=limit,
                             timeout=self.timeout, input_bytes=input_bytes)

    def run(self, args, *, input_bytes=None, limit=None):
        with self.open(args, limit=self.json_limit if limit is None else limit,
                       input_bytes=input_bytes) as stream:
            return stream.read()


class GhClient:
    """Exact gh CLI mapping, github.com only. No create, publish, delete or clobber."""
    def __init__(self, runner: GhRunner, release_id=None):
        if release_id is not None and (type(release_id) is not int or release_id < 1):
            raise ValueError('Invalid release ID')
        self.runner, self.release_id = runner, release_id

    def _args(self, endpoint):
        return ['api', '--hostname', 'github.com', '-H', 'X-GitHub-Api-Version: 2022-11-28', endpoint]

    def _json(self, args, payload=None):
        data = self.runner.run(args, input_bytes=None if payload is None else json.dumps(payload).encode())
        try:
            return json.loads(data)
        except (ValueError, UnicodeError):
            raise SinkError('Invalid bounded gh JSON metadata') from None

    def release(self, repo, tag):
        if self.release_id is not None:
            return self._json(self._args(f'/repos/{repo}/releases/{self.release_id}'))
        return self._json(self._args(f'/repos/{repo}/releases/tags/{quote(tag, safe="")}'))

    def assets(self, repo, release_id, page):
        return self._json(self._args(f'/repos/{repo}/releases/{release_id}/assets?per_page=100&page={page}'))

    def upload(self, repo, release_id, path):
        # Explicit github.com credential host; pinned numeric release, no tag lookup.
        endpoint = (f'https://uploads.github.com/repos/{repo}/releases/{release_id}/assets'
                    f'?name={quote(path.name, safe="")}')
        self.runner.run([*self._args(endpoint), '--method', 'POST', '--input', str(path),
                         '-H', 'Content-Type: application/octet-stream'], limit=65536)

    def rename(self, repo, asset_id, name):
        args = self._args(f'/repos/{repo}/releases/assets/{asset_id}')
        self._json([*args, '--method', 'PATCH', '--input', '-', '-H', 'Content-Type: application/json'], {'name': name})

    def open_asset(self, repo, asset_id, size):
        return self.runner.open([*self._args(f'/repos/{repo}/releases/assets/{asset_id}'),
                                 '-H', 'Accept: application/octet-stream'], limit=size)


def checksum(stream):
    size, h = 0, hashlib.sha256()
    while block := stream.read(BLOCK):
        size += len(block)
        h.update(block)
    return size, h.hexdigest()


def file_checksum(path):
    with Path(path).open('rb') as stream:
        return checksum(stream)


def positive_int(value):
    return type(value) is int and value > 0


class GitHubReleaseSink:
    """One immutable cache bundle in one explicitly pre-existing draft release.

    The required client argument makes network capability an explicit choice.
    The constructor pins release id as well as exact tag/repo. Existing equal
    bytes permit idempotent reconciliation; different bytes NEVER get replaced.
    """
    def __init__(self, repo, tag, *, client: GhClient, mutation_attempts=2):
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*', repo):
            raise ValueError('Explicit owner/repo required')
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_./+\-]*', tag) or '..' in tag.split('/'):
            raise ValueError('Explicit safe release tag required')
        if type(mutation_attempts) is not int or not 1 <= mutation_attempts <= 3:
            raise ValueError('Invalid bounded mutation attempts')
        self.repo, self.tag, self.client = repo, tag, client
        self.mutation_attempts, self.release_id = mutation_attempts, None
        self._draft()

    def _draft(self):
        r = self.client.release(self.repo, self.tag)
        if not isinstance(r, dict) or r.get('draft') is not True or r.get('tag_name') != self.tag or not positive_int(r.get('id')):
            raise DraftRequired('Exact pre-existing draft release required')
        if self.release_id is None:
            self.release_id = r['id']
        elif self.release_id != r['id']:
            raise DraftRequired('Pinned release id changed')

    def _assets(self):
        self._draft()
        result = []
        for page in range(1, 101):
            rows = self.client.assets(self.repo, self.release_id, page)
            if not isinstance(rows, list) or len(rows) > 100 or any(not isinstance(a, dict) for a in rows):
                raise SinkError('Invalid asset metadata page')
            result.extend(rows)
            if len(rows) < 100:
                return result
        raise SinkError('Asset listing exceeded bounded pagination')

    def _find(self, name, rows=None):
        matches = [a for a in (self._assets() if rows is None else rows) if a.get('name') == name]
        if len(matches) > 1:
            raise Conflict('Ambiguous duplicate asset name')
        return matches[0] if matches else None

    def _open(self, asset, limit):
        if (not positive_int(asset.get('id')) or asset.get('state') != 'uploaded'
                or type(asset.get('size')) is not int or not 0 <= asset['size'] <= limit):
            raise Conflict('Asset is incomplete or exceeds its size bound')
        self._draft()
        return self.client.open_asset(self.repo, asset['id'], asset['size'])

    def _verify(self, asset, spec, limit):
        with self._open(asset, limit) as stream:
            if checksum(stream) != (spec['bytes'], spec['sha256']):
                raise Conflict('Remote asset bytes differ from immutable descriptor')
        self._draft()

    def _spec(self, path, descriptor, manifest=False):
        if not isinstance(descriptor, dict):
            raise ValueError('Descriptor required')
        name, size, digest = (descriptor.get(k) for k in ('name', 'bytes', 'sha256'))
        if manifest:
            valid = name == 'cache.json'
        else:
            valid = isinstance(name, str) and re.fullmatch(r'cache-[0-9]{6}\.tar\.zst\.part', name)
        limit = MAX_MANIFEST if manifest else MAX_PART
        if (not valid or type(size) is not int or not 0 <= size <= limit
                or not isinstance(digest, str) or not re.fullmatch(r'[0-9a-f]{64}', digest)):
            raise ValueError('Invalid immutable asset descriptor')
        if file_checksum(path) != (size, digest):
            raise ValueError('Local file differs from immutable descriptor')
        return {'name': name, 'bytes': size, 'sha256': digest}, limit

    def _put(self, path, spec, limit):
        for attempt in range(self.mutation_attempts):
            existing = self._find(spec['name'])
            if existing is not None:
                self._verify(existing, spec, limit)
                return existing
            self._draft()
            failed = None
            # Hard-link alias preserves bounded spool usage, even for a full part.
            with tempfile.TemporaryDirectory(prefix='.gh-release-', dir=Path(path).resolve().parent) as td:
                alias = Path(td)/spec['name']
                os.link(Path(path).resolve(), alias)
                try:
                    self.client.upload(self.repo, self.release_id, alias)
                except Exception as error:
                    failed = error
            try:
                existing = self._find(spec['name'])
            except Exception as error:
                raise UncertainMutation('Upload state could not be reconciled; no retry') from error
            if existing is not None:
                self._verify(existing, spec, limit)
                return existing
            if failed is None:
                raise UncertainMutation('Upload returned success but no completed asset is visible')
            # A missing asset was actually read before the next mutation attempt.
            if attempt+1 == self.mutation_attempts:
                raise UncertainMutation('Upload failed and asset remains absent') from failed
        raise AssertionError('Unreachable')

    def put_part(self, path, descriptor):
        spec, limit = self._spec(path, descriptor)
        self._put(path, spec, limit)

    def open_part(self, name):
        if not isinstance(name, str) or not re.fullmatch(r'cache-[0-9]{6}\.tar\.zst\.part', name):
            raise ValueError('Invalid part name')
        asset = self._find(name)
        if asset is None:
            raise FileNotFoundError(name)
        return self._open(asset, MAX_PART)

    def commit_manifest(self, path, descriptor):
        spec, limit = self._spec(path, descriptor, manifest=True)
        existing = self._find('cache.json')
        if existing is not None:
            self._verify(existing, spec, limit)
            return
        stage = dict(spec, name='cache-manifest-'+spec['sha256']+'.staging.json')
        asset = self._put(path, stage, limit)  # independently read/hash staged bytes
        stage_id = asset['id']
        for attempt in range(self.mutation_attempts):
            rows = self._assets()
            final = self._find('cache.json', rows)
            if final is not None:
                self._verify(final, spec, limit)
                return
            current = self._find(stage['name'], rows)
            if current is None or current.get('id') != stage_id:
                raise UncertainMutation('Verified staging asset identity changed')
            self._verify(current, stage, limit)
            self._draft()
            failed = None
            try:
                # GitHub rejects a destination name owned by another asset.
                # No delete, rename-away, clobber, or release mutation is used.
                self.client.rename(self.repo, stage_id, 'cache.json')
            except Exception as error:
                failed = error
            try:
                rows = self._assets()
                final = self._find('cache.json', rows)
            except Exception as error:
                raise UncertainMutation('Rename state could not be reconciled; no retry') from error
            if final is not None:
                self._verify(final, spec, limit)
                return
            current = self._find(stage['name'], rows)
            if current is None or current.get('id') != stage_id:
                raise UncertainMutation('Staging asset vanished after rename')
            if attempt+1 == self.mutation_attempts:
                raise UncertainMutation('Manifest rename did not commit') from failed
            # Actual same-stage/no-canonical state was read before retrying.

    def open_manifest(self):
        asset = self._find('cache.json')
        if asset is None:
            raise FileNotFoundError('cache.json')
        return self._open(asset, MAX_MANIFEST)
