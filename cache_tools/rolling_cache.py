#!/usr/bin/env python3
"""Bounded-spool cache publisher and streaming verifier; filesystem mock only CLI.

The sink protocol is pluggable. No network or GitHub operations are implemented.
A sink must commit the exact verified manifest atomically or leave it absent.
"""
import argparse
import hashlib
import importlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
from typing import BinaryIO, Protocol

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).parent / 'vendor'))
merger = importlib.import_module('merge_cache')
BLOCK = 64 * 1024
MAX_CHUNK = 95 * 1024 * 1024


def checksum(stream):
    h, size = hashlib.sha256(), 0
    while data := stream.read(BLOCK):
        h.update(data)
        size += len(data)
    return size, h.hexdigest()


def file_checksum(path):
    with Path(path).open('rb') as stream:
        return checksum(stream)


def atomic_json(path, data):
    path = Path(path)
    temporary = path.with_name(path.name + '.pending')
    with temporary.open('xb') as stream:
        stream.write(json.dumps(data, indent=2, sort_keys=True).encode() + b'\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def safe_path(name):
    path = PurePosixPath(name)
    canonical = name.rstrip('/')
    if (not canonical or '\x00' in name or '\\' in name or path.is_absolute()
            or '..' in path.parts or str(path) != canonical or str(path) == '.'):
        raise ValueError(f'Unsafe or noncanonical path: {name!r}')
    return path


class Sink(Protocol):
    def put_part(self, path: Path, descriptor: dict) -> None: ...
    def open_part(self, name: str) -> BinaryIO: ...
    def commit_manifest(self, path: Path, descriptor: dict) -> None: ...
    def open_manifest(self) -> BinaryIO: ...


class DirectorySink:
    """Mock remote: immutable parts, verified atomic final manifest, no uploads."""
    def __init__(self, directory):
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.events = []

    def _put(self, path, descriptor):
        name = descriptor['name']
        if safe_path(name).name != name:
            raise ValueError('Sink names must be basenames')
        target = self.directory / name
        pending = self.directory / (name + '.pending')
        with Path(path).open('rb') as source, pending.open('xb') as dest:
            shutil.copyfileobj(source, dest, BLOCK)
            dest.flush()
            os.fsync(dest.fileno())
        if file_checksum(pending) != (descriptor['bytes'], descriptor['sha256']):
            pending.unlink()
            raise ValueError('Staged sink bytes do not match descriptor')
        # Hard-link commit is atomic and refuses an existing immutable destination.
        os.link(pending, target)
        pending.unlink()
        fd = os.open(self.directory, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
        self.events.append(name)

    def put_part(self, path, descriptor):
        self._put(path, descriptor)

    def open_part(self, name):
        if safe_path(name).name != name:
            raise ValueError('Invalid part name')
        return (self.directory / name).open('rb')

    def commit_manifest(self, path, descriptor):
        if descriptor['name'] != 'cache.json':
            raise ValueError('Invalid manifest name')
        self._put(path, descriptor)

    def open_manifest(self):
        return (self.directory / 'cache.json').open('rb')


class TeeReader:
    def __init__(self, source, destination):
        self.source, self.destination = source, destination

    def read(self, size=-1):
        data = self.source.read(size)
        if data:
            self.destination.write(data)
        return data


def audit_tar(stream, roots, expected=None):
    """Consume every member and full trailing padding without extracting files."""
    allowed = [safe_path(root) for root in roots]
    if not allowed or len(set(allowed)) != len(allowed):
        raise ValueError('Invalid roots')
    seen, members, directories = set(), {}, {}
    # bufsize=512 avoids hiding arbitrary bytes past the archive terminator.
    with tarfile.open(fileobj=stream, mode='r|', bufsize=512) as archive:
        for member in archive:
            path = safe_path(member.name)
            key = str(path)
            if path in seen:
                raise ValueError(f'Duplicate tar member: {key}')
            if not any(path.is_relative_to(root) for root in allowed):
                raise ValueError(f'Member outside pinned roots: {key}')
            if not (member.isfile() or member.isdir()):
                raise ValueError(f'Unsafe tar member type: {key}')
            seen.add(path)
            if member.isdir():
                directories[key] = member.mode
            else:
                with archive.extractfile(member) as data:
                    size, sha = checksum(data)
                if size != member.size:
                    raise ValueError(f'Truncated tar member: {key}')
                members[key] = {'bytes': size, 'sha256': sha, 'mode': member.mode}
        # tarfile has consumed one zero end-block; inspect buffered remainder too.
        while remainder := archive.fileobj.read(BLOCK):
            if any(remainder):
                raise ValueError('Nonzero trailing bytes after tar terminator')
    while block := stream.read(BLOCK):
        if any(block):
            raise ValueError('Nonzero trailing bytes after tar terminator')
    if not all(str(root) in directories for root in allowed):
        raise ValueError('Missing pinned root directory')
    result = {'members': members, 'directories': directories}
    if expected is not None and result != expected:
        raise ValueError('Full tar member set/size/hash/mode mismatch')
    return result


def stop(process):
    if process is None:
        return
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()


def validate_parts(sink, manifest, scratch):
    """Stream parts from any Sink through zstd and a full non-extracting tar audit."""
    if manifest.get('version') != 1 or manifest.get('rolling_format_version') != 1:
        raise ValueError('Unsupported manifest format')
    chunks = manifest['chunks']
    if not chunks:
        raise ValueError('No chunks')
    for i, row in enumerate(chunks):
        if (row['name'] != f'cache-{i:06}.tar.zst.part'
                or not 0 < row['bytes'] <= MAX_CHUNK
                or len(row['sha256']) != 64):
            raise ValueError('Invalid ordered chunk descriptor')
    scratch = Path(scratch)
    errors = []
    with (scratch / 'validate-zstd.log').open('wb') as log:
        decoder = subprocess.Popen(['zstd', '-qdc'], stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=log, start_new_session=True)
        def download():
            try:
                for row in chunks:
                    h, size = hashlib.sha256(), 0
                    with sink.open_part(row['name']) as source:
                        while data := source.read(BLOCK):
                            size += len(data)
                            if size > row['bytes']:
                                raise ValueError('Remote part exceeds recorded size')
                            h.update(data)
                            decoder.stdin.write(data)
                    if (size, h.hexdigest()) != (row['bytes'], row['sha256']):
                        raise ValueError('Remote part size/hash mismatch')
            except BaseException as error:
                errors.append(error)
            finally:
                try:
                    decoder.stdin.close()
                except OSError as error:
                    errors.append(error)
        worker = threading.Thread(target=download, daemon=True)
        worker.start()
        try:
            actual = audit_tar(decoder.stdout, manifest['identity']['roots'],
                               {'members': manifest['members'], 'directories': manifest['directories']})
            worker.join(timeout=10)
            if worker.is_alive():
                raise RuntimeError('Part reader failed to finish')
            if errors:
                raise errors[0]
            if decoder.wait() != 0:
                raise ValueError('Full zstd stream failed verification')
            return actual
        finally:
            stop(decoder)
            decoder.stdout.close()
            worker.join(timeout=10)


def validate_sink(sink, trusted_manifest_sha256, scratch):
    with sink.open_manifest() as stream:
        content = stream.read(64 * 1024 * 1024 + 1)
    if len(content) > 64 * 1024 * 1024:
        raise ValueError('Manifest too large')
    if hashlib.sha256(content).hexdigest() != trusted_manifest_sha256:
        raise ValueError('Untrusted manifest digest')
    manifest = json.loads(content)
    validate_parts(sink, manifest, scratch)
    return manifest


def _publish_merged(project, identity, checkpoints, sink, spool, chunk_bytes=MAX_CHUNK):
    """Internal engine; production caller must obtain identity from cache.identity."""
    if not 0 < chunk_bytes <= MAX_CHUNK:
        raise ValueError('Invalid part limit')
    spool = Path(spool).resolve()
    project = Path(project).resolve()
    for root in identity['roots']:
        build = (project / safe_path(root)).resolve()
        if spool.is_relative_to(build):
            raise ValueError('Spool must be outside every producer build root')
        if isinstance(sink, DirectorySink) and sink.directory.resolve().is_relative_to(build):
            raise ValueError('Mock destination must be outside producer build roots')
    if isinstance(sink, DirectorySink):
        destination = sink.directory.resolve()
        if spool.is_relative_to(destination) or destination.is_relative_to(spool):
            raise ValueError('Spool and mock destination must be disjoint')
    try:
        existing = sink.open_manifest()
    except FileNotFoundError:
        pass
    else:
        existing.close()
        raise ValueError('Destination already has a final manifest')
    spool.mkdir(parents=True, exist_ok=False)
    receipt = {'status': 'incomplete', 'verified_parts': [], 'spool_peak_parts': 0, 'spool_peak_part_bytes': 0}
    atomic_json(spool / 'receipt.json', receipt)
    if any(mount not in {safe_path(r) / 'ir' for r in identity['roots']}
           for mount, _, _, _ in checkpoints):
        raise ValueError('Sidecar mount outside pinned IR roots')
    request = {'roots': identity['roots'], 'base_chunks': [], 'checkpoints':
               [[str(mount), str(archive), metadata, sorted(removed)]
                for mount, archive, metadata, removed in checkpoints]}
    producer = encoder = None
    worker = None
    errors, audit = [], []
    try:
        with (spool / 'producer.log').open('wb') as plog, (spool / 'compress.log').open('wb') as elog:
            env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
            producer = subprocess.Popen([sys.executable, merger.__file__, '_tar', '--project', str(project)],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=plog,
                                        env=env, start_new_session=True)
            encoder = subprocess.Popen(['zstd', '-q', '-T1', '-c'], stdin=subprocess.PIPE,
                                       stdout=subprocess.PIPE, stderr=elog, start_new_session=True)
            producer.stdin.write(json.dumps(request).encode())
            producer.stdin.close()
            def inspect():
                try:
                    audit.append(audit_tar(TeeReader(producer.stdout, encoder.stdin), identity['roots']))
                except BaseException as error:
                    errors.append(error)
                finally:
                    try:
                        encoder.stdin.close()
                    except OSError as error:
                        errors.append(error)
            worker = threading.Thread(target=inspect, daemon=True)
            worker.start()
            while first := encoder.stdout.read(min(BLOCK, chunk_bytes)):
                number = len(receipt['verified_parts'])
                name = f'cache-{number:06}.tar.zst.part'
                part = spool / name
                size, h = 0, hashlib.sha256()
                with part.open('xb') as file:
                    data = first
                    while data:
                        file.write(data)
                        size += len(data)
                        h.update(data)
                        if size == chunk_bytes:
                            break
                        data = encoder.stdout.read(min(BLOCK, chunk_bytes-size))
                    file.flush()
                    os.fsync(file.fileno())
                row = {'name': name, 'bytes': size, 'sha256': h.hexdigest()}
                parts = list(spool.glob('cache-*.part'))
                receipt['spool_peak_parts'] = max(receipt['spool_peak_parts'], len(parts))
                receipt['spool_peak_part_bytes'] = max(receipt['spool_peak_part_bytes'], sum(p.stat().st_size for p in parts))
                sink.put_part(part, row)
                with sink.open_part(name) as remote:
                    if checksum(remote) != (size, row['sha256']):
                        raise ValueError('Part readback size/hash mismatch')
                receipt['verified_parts'].append(row)
                atomic_json(spool / 'receipt.json', receipt)
                part.unlink()  # Only after independently reading the sink's exact bytes.
            worker.join(timeout=10)
            if worker.is_alive():
                raise RuntimeError('Tar audit worker failed to finish')
            if errors:
                raise errors[0]
            if encoder.wait() != 0 or producer.wait() != 0 or not audit:
                raise RuntimeError('Original merge/compression stream failed')
        manifest = {'version': 1, 'rolling_format_version': 1, 'identity': identity,
                    'chunks': receipt['verified_parts'], **audit[0],
                    'setup_checkpoints': [{'mount': str(m), 'archive_sha256': md['archive_sha256'],
                                           'removed': sorted(r)} for m, _, md, r in checkpoints]}
        # Full roundtrip of ALL remote/mock parts, roots, types and file hashes BEFORE committing manifest.
        validate_parts(sink, manifest, spool)
        local_manifest = spool / 'cache-manifest.candidate.json'
        atomic_json(local_manifest, manifest)
        size, sha = file_checksum(local_manifest)
        sink.commit_manifest(local_manifest, {'name': 'cache.json', 'bytes': size, 'sha256': sha})
        with sink.open_manifest() as stream:
            if checksum(stream) != (size, sha):
                raise ValueError('Atomic manifest commit violated sink contract')
        receipt.update(status='complete', manifest_sha256=sha,
                       member_count=len(manifest['members']), raw_bytes=sum(r['bytes'] for r in manifest['members'].values()))
        atomic_json(spool / 'receipt.json', receipt)
        return receipt
    except BaseException as error:
        receipt['error'] = f'{type(error).__name__}: {error}'
        atomic_json(spool / 'receipt.json', receipt)
        raise
    finally:
        stop(producer)
        stop(encoder)
        if worker is not None:
            worker.join(timeout=10)
        for process in (producer, encoder):
            if process is not None and process.stdout is not None:
                process.stdout.close()


def publish_project(project, lean, sidecars, sink, spool, chunk_bytes=MAX_CHUNK):
    identity = merger.identity(Path(project).resolve(), Path(lean).resolve())
    checkpoints = [merger.batch(root, Path(prune), Path(metadata)) for root, prune, metadata in sidecars]
    return _publish_merged(Path(project).resolve(), identity, checkpoints, sink, spool, chunk_bytes)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='action', required=True)
    pack = sub.add_parser('pack-mock')
    pack.add_argument('--project', type=Path, required=True)
    pack.add_argument('--lean', type=Path, required=True)
    pack.add_argument('--sidecar', nargs=3, action='append', default=[])
    pack.add_argument('--sink', type=Path, required=True)
    pack.add_argument('--spool', type=Path, required=True)
    pack.add_argument('--chunk-bytes', type=int, default=MAX_CHUNK)
    verify = sub.add_parser('verify-mock')
    verify.add_argument('--sink', type=Path, required=True)
    verify.add_argument('--manifest-sha256', required=True)
    verify.add_argument('--scratch', type=Path, required=True)
    args = p.parse_args()
    if args.action == 'pack-mock':
        result = publish_project(args.project, args.lean, args.sidecar, DirectorySink(args.sink), args.spool, args.chunk_bytes)
    else:
        args.scratch.mkdir(parents=True, exist_ok=True)
        m = validate_sink(DirectorySink(args.sink), args.manifest_sha256, args.scratch)
        result = {'status': 'verified', 'members': len(m['members']), 'chunks': len(m['chunks'])}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
