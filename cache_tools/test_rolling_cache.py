import copy
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest

sys.dont_write_bytecode = True
import rolling_cache as rc

ROOT = '.lake/build'
IR = ROOT + '/ir'


def zstd(data):
    return subprocess.run(['zstd', '-q', '-T1', '-c'], input=data, capture_output=True, check=True).stdout


def raw_tar(entries):
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode='w') as archive:
        for name, content, kind in entries:
            item = tarfile.TarInfo(name)
            item.mode = 0o755 if kind == 'dir' else 0o644
            if kind == 'dir':
                item.type = tarfile.DIRTYPE
                archive.addfile(item)
            elif kind == 'link':
                item.type = tarfile.SYMTYPE
                item.linkname = '/outside'
                archive.addfile(item)
            else:
                item.size = len(content)
                archive.addfile(item, io.BytesIO(content))
    return out.getvalue()


def sidecar(directory, members, removed):
    directory.mkdir()
    payload = zstd(raw_tar([(name, value, 'file') for name, value in members.items()]))
    (directory / 'setup.tar.zst').write_bytes(payload)
    metadata = {'archive_sha256': hashlib.sha256(payload).hexdigest(),
                'files': {name: {'size': len(value), 'sha256': hashlib.sha256(value).hexdigest()}
                          for name, value in members.items()}}
    (directory / 'setup.json').write_text(json.dumps(metadata))
    (directory / 'pruned.json').write_text(json.dumps({'archive': 'setup.tar.zst', 'removed': removed}))
    return rc.merger.batch(IR, directory / 'pruned.json', directory / 'setup.json')


class FailingSink(rc.DirectorySink):
    def __init__(self, directory, fail_part=None, fail_manifest=False, corrupt_readback=False):
        super().__init__(directory)
        self.calls = 0
        self.fail_part = fail_part
        self.fail_manifest = fail_manifest
        self.corrupt_readback = corrupt_readback

    def put_part(self, path, descriptor):
        self.calls += 1
        # Callback sees exactly one finalized local compressed part and no growing next part.
        if len(list(path.parent.glob('cache-*.part'))) != 1:
            raise AssertionError('More than one local spool part')
        if rc.file_checksum(path) != (descriptor['bytes'], descriptor['sha256']):
            raise AssertionError('Callback received unfinished part')
        if self.calls == self.fail_part:
            raise RuntimeError('induced upload failure')
        super().put_part(path, descriptor)

    def open_part(self, name):
        if self.corrupt_readback:
            content = (self.directory / name).read_bytes()
            return io.BytesIO(bytes([content[0] ^ 1]) + content[1:])
        return super().open_part(name)

    def commit_manifest(self, path, descriptor):
        if self.fail_manifest:
            raise RuntimeError('induced manifest failure')
        super().commit_manifest(path, descriptor)


class RollingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='fixture-', dir=Path(__file__).parent)
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.project = self.base / 'project'
        (self.project / IR).mkdir(parents=True)
        (self.project / IR / 'live.setup.json').write_bytes(b'LIVE-WINS')
        (self.project / ROOT / 'payload.olean').write_bytes(bytes(range(256)) * 64)
        # Incompressible deterministic bytes ensure several tiny compressed parts.
        (self.project / ROOT / 'noise.bin').write_bytes(b''.join(hashlib.sha256(str(i).encode()).digest() for i in range(128)))
        self.old = sidecar(self.base / 'old', {'live.setup.json': b'OLD-LIVE',
                          'missing.setup.json': b'OLD', 'old-only.setup.json': b'OLD-ONLY',
                          'unlisted.setup.json': b'MUST-NOT-PUBLISH'},
                          ['live.setup.json', 'missing.setup.json', 'old-only.setup.json'])
        self.new = sidecar(self.base / 'new', {'live.setup.json': b'NEW-BUT-NOT-LIVE',
                          'missing.setup.json': b'NEWEST'}, ['live.setup.json', 'missing.setup.json'])
        self.identity = {'roots': [ROOT], 'fixture_only': 'tiny non-Lean payloads; no production identity claim'}

    def publish(self, sink=None):
        sink = sink or FailingSink(self.base / 'remote')
        receipt = rc._publish_merged(self.project, self.identity, [self.old, self.new], sink, self.base / 'spool', 256)
        return sink, receipt

    def test_full_roundtrip_live_newest_precedence_one_part_and_manifest_last(self):
        sink, receipt = self.publish()
        self.assertEqual(receipt['status'], 'complete')
        self.assertEqual(receipt['spool_peak_parts'], 1)
        self.assertEqual(receipt['spool_peak_part_bytes'], 256)
        self.assertFalse(list((self.base / 'spool').glob('cache-*.part')))
        self.assertGreater(len(receipt['verified_parts']), 3)
        self.assertEqual(sink.events[-1], 'cache.json')
        self.assertEqual(len(sink.events), len(receipt['verified_parts']) + 1)
        check = self.base / 'check'
        check.mkdir()
        manifest = rc.validate_sink(sink, receipt['manifest_sha256'], check)
        files = manifest['members']
        for name, expected in [('live.setup.json', b'LIVE-WINS'), ('missing.setup.json', b'NEWEST'), ('old-only.setup.json', b'OLD-ONLY')]:
            self.assertEqual(files[IR + '/' + name]['sha256'], hashlib.sha256(expected).hexdigest())
        self.assertNotIn(IR + '/unlisted.setup.json', files)
        # Existing companion verify accepts the augmented regular version-1 bundle.
        self.assertEqual(rc.merger.verify(sink.directory)['chunks'], receipt['verified_parts'])

    def test_production_identity_failure_does_not_publish(self):
        from unittest.mock import patch
        sink = rc.DirectorySink(self.base / 'identity-failure')
        with patch.object(rc.merger, 'identity', side_effect=ValueError('dirty source')) as identity:
            with self.assertRaisesRegex(ValueError, 'dirty source'):
                rc.publish_project(self.project, self.base / 'lean', [], sink, self.base / 'no-spool')
            identity.assert_called_once()
        self.assertFalse(sink.events)
        self.assertFalse((self.base / 'no-spool').exists())

    def test_spool_inside_build_and_existing_complete_destination_rejected(self):
        sink = rc.DirectorySink(self.base / 'remote')
        with self.assertRaisesRegex(ValueError, 'outside every producer'):
            rc._publish_merged(self.project, self.identity, [], sink, self.project / ROOT / 'bad-spool', 256)
        self.publish(sink)
        with self.assertRaisesRegex(ValueError, 'already has a final manifest'):
            rc._publish_merged(self.project, self.identity, [], sink, self.base / 'another-spool', 256)
        self.assertEqual(sink.events[-1], 'cache.json')

    def test_upload_failure_leaves_incomplete_and_failed_spool_part(self):
        sink = FailingSink(self.base / 'remote', fail_part=2)
        with self.assertRaisesRegex(RuntimeError, 'induced upload'):
            self.publish(sink)
        self.assertFalse((sink.directory / 'cache.json').exists())
        receipt = json.loads((self.base / 'spool/receipt.json').read_text())
        self.assertEqual(receipt['status'], 'incomplete')
        self.assertEqual(len(receipt['verified_parts']), 1)
        self.assertEqual(len(list((self.base / 'spool').glob('cache-*.part'))), 1)

    def test_readback_mismatch_never_commits_manifest(self):
        sink = FailingSink(self.base / 'remote', corrupt_readback=True)
        with self.assertRaisesRegex(ValueError, 'readback'):
            self.publish(sink)
        self.assertFalse((sink.directory / 'cache.json').exists())
        self.assertEqual(len(list((self.base / 'spool').glob('cache-*.part'))), 1)

    def test_manifest_failure_stays_incomplete(self):
        sink = FailingSink(self.base / 'remote', fail_manifest=True)
        with self.assertRaisesRegex(RuntimeError, 'manifest failure'):
            self.publish(sink)
        self.assertFalse((sink.directory / 'cache.json').exists())
        self.assertEqual(json.loads((self.base / 'spool/receipt.json').read_text())['status'], 'incomplete')
        self.assertFalse(list((self.base / 'spool').glob('cache-*.part')))

    def test_trusted_manifest_digest_required(self):
        sink, _ = self.publish()
        with self.assertRaisesRegex(ValueError, 'Untrusted manifest'):
            rc.validate_sink(sink, '0' * 64, self.base)

    def test_full_member_hash_verified_independent_of_chunk_hash(self):
        sink, _ = self.publish()
        manifest = json.loads((sink.directory / 'cache.json').read_text())
        member = next(iter(manifest['members'].values()))
        member['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'member set/size/hash/mode'):
            rc.validate_parts(sink, manifest, self.base)

    def test_modified_remote_chunk_rejected(self):
        sink, _ = self.publish()
        manifest = json.loads((sink.directory / 'cache.json').read_text())
        # Replace a compressed-frame byte; do not update its trusted descriptor.
        part = sink.directory / manifest['chunks'][0]['name']
        content = part.read_bytes()
        part.write_bytes(bytes([content[0] ^ 1]) + content[1:])
        with self.assertRaises((ValueError, tarfile.ReadError, EOFError)):
            rc.validate_parts(sink, manifest, self.base)

    def attack(self, entries):
        remote = self.base / 'attack'
        remote.mkdir()
        content = zstd(raw_tar(entries))
        name = 'cache-000000.tar.zst.part'
        (remote / name).write_bytes(content)
        manifest = {'version': 1, 'rolling_format_version': 1, 'identity': self.identity,
                    'chunks': [{'name': name, 'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()}],
                    'members': {}, 'directories': {ROOT: 0o755}}
        return rc.DirectorySink(remote), manifest

    def test_unsafe_path_duplicate_and_link_rejected_in_stream(self):
        for index, extra in enumerate([
            [(ROOT + '/../escape', b'bad', 'file')],
            [('/absolute', b'bad', 'file')],
            [(ROOT + '/x', b'a', 'file'), (ROOT + '/x', b'b', 'file')],
            [(ROOT + '/link', b'', 'link')],
        ]):
            with self.subTest(attack=index):
                sink, manifest = self.attack([(ROOT, b'', 'dir')] + extra)
                with self.assertRaisesRegex(ValueError, 'Unsafe|Duplicate'):
                    rc.validate_parts(sink, manifest, self.base)
                shutil = __import__('shutil')
                shutil.rmtree(sink.directory)

    def test_truncated_zstd_frame_rejected_even_when_member_bytes_survive(self):
        sink, _ = self.publish()
        manifest = json.loads((sink.directory / 'cache.json').read_text())
        row = manifest['chunks'][-1]
        path = sink.directory / row['name']
        shortened = path.read_bytes()[:-1]
        self.assertTrue(shortened)
        path.write_bytes(shortened)
        row.update(bytes=len(shortened), sha256=hashlib.sha256(shortened).hexdigest())
        with self.assertRaises((ValueError, tarfile.ReadError, EOFError)):
            rc.validate_parts(sink, manifest, self.base)


if __name__ == '__main__':
    unittest.main(verbosity=2)
