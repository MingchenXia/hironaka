import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import github_release_sink as g

HERE = Path(__file__).parent


def descriptor(name, data):
    return {'name': name, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


class FakeClient:
    """Stateful API model: unique immutable contents; server rename is no-clobber."""
    def __init__(self):
        self.release_data = {'id': 7, 'tag_name': 'cache/test-1', 'draft': True}
        self.items, self.calls, self.next_id = [], [], 1
        self.upload_before = self.upload_after = self.rename_before = self.rename_after = 0
        self.fail_reconcile = False
        self.fail_rename_reconcile = False
        self.rename_mutated = False
        self.mutated = False
        self.corrupt_stage = False
        self.before_rename = None

    def add(self, name, data, state='uploaded'):
        x = {'id': self.next_id, 'name': name, 'size': len(data), 'state': state, 'data': data}
        self.next_id += 1; self.items.append(x)
        return x

    def release(self, repo, tag):
        self.calls.append(('release', repo, tag))
        return dict(self.release_data)

    def assets(self, repo, ident, page):
        self.calls.append(('assets', page))
        if (self.fail_reconcile and self.mutated) or (self.fail_rename_reconcile and self.rename_mutated): raise g.GhFailure(1)
        return [dict(x) for x in self.items[(page-1)*100:page*100]]

    def upload(self, repo, tag, path):
        self.calls.append(('upload', path.name))
        if self.upload_before:
            self.upload_before -= 1; raise g.GhFailure(1)
        if any(x['name'] == path.name for x in self.items): raise g.GhFailure(1)
        data = path.read_bytes()
        if self.corrupt_stage and '.staging.' in path.name: data += b'corrupt'
        self.add(path.name, data); self.mutated = True
        if self.upload_after:
            self.upload_after -= 1; raise g.GhFailure(1)

    def rename(self, repo, ident, name):
        self.calls.append(('rename', ident, name))
        if self.before_rename: self.before_rename(self)
        if self.rename_before:
            self.rename_before -= 1; raise g.GhFailure(1)
        if any(x['name'] == name and x['id'] != ident for x in self.items): raise g.GhFailure(1)
        x = next(x for x in self.items if x['id'] == ident)
        x['name'] = name; self.mutated = True; self.rename_mutated = True
        if self.rename_after:
            self.rename_after -= 1; raise g.GhFailure(1)

    def open_asset(self, repo, ident, size):
        self.calls.append(('read', ident))
        return io.BytesIO(next(x['data'] for x in self.items if x['id'] == ident))


class SinkTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.client = FakeClient()
        self.sink = g.GitHubReleaseSink('o/r', 'cache/test-1', client=self.client)

    def file(self, name, data):
        p = self.root/name; p.write_bytes(data); return p

    def part(self, data=b'PART'):
        p = self.file('local-input', data)
        spec = descriptor('cache-000000.tar.zst.part', data)
        return p, spec

    def manifest(self, data=b'{"version":1}'):
        return self.file('local-manifest', data), descriptor('cache.json', data)

    def test_exact_draft_repo_tag_id_and_shape_guards(self):
        for change in [{'draft': False}, {'draft': 1}, {'tag_name': 'different'}, {'id': True}]:
            with self.subTest(change=change):
                c = FakeClient(); c.release_data.update(change)
                with self.assertRaises(g.DraftRequired): g.GitHubReleaseSink('o/r', 'cache/test-1', client=c)
        for repo, tag in [('o/r/x', 'x'), ('o/r', '--bad'), ('o/r', 'bad tag'), ('o/r', '../bad')]:
            with self.assertRaises(ValueError): g.GitHubReleaseSink(repo, tag, client=self.client)
        self.client.release_data['id'] = 8
        with self.assertRaises(g.DraftRequired): self.sink.open_manifest()

    def test_parts_immutable_and_independent_full_readback(self):
        p, spec = self.part()
        self.sink.put_part(p, spec)
        with self.sink.open_part(spec['name']) as stream: self.assertEqual(stream.read(), b'PART')
        before = list(self.client.calls)
        self.sink.put_part(p, spec)
        self.assertEqual(sum(c[0] == 'upload' for c in self.client.calls), 1)
        p.write_bytes(b'ELSE')
        with self.assertRaises(g.Conflict): self.sink.put_part(p, descriptor(spec['name'], b'ELSE'))
        self.assertEqual(self.client.items[0]['data'], b'PART')
        self.assertTrue(before)

    def test_bad_local_descriptor_no_mutation(self):
        p, spec = self.part(); spec['sha256'] = '0'*64
        with self.assertRaises(ValueError): self.sink.put_part(p, spec)
        self.assertFalse(self.client.items)
        for name in ['../x', 'cache.json', '--clobber', 'a#label', 'cache-1.tar.zst.part']:
            with self.assertRaises(ValueError): self.sink.put_part(p, descriptor(name, b'PART'))
        self.assertFalse(any(c[0] == 'upload' for c in self.client.calls))

    def test_upload_lost_response_is_reconciled_not_duplicated(self):
        self.client.upload_after = 1
        self.sink.put_part(*self.part())
        self.assertEqual(sum(c[0] == 'upload' for c in self.client.calls), 1)

    def test_upload_retry_reads_state_between_attempts(self):
        self.client.upload_before = 1
        self.sink.put_part(*self.part())
        places = [i for i,c in enumerate(self.client.calls) if c[0] == 'upload']
        self.assertEqual(len(places), 2)
        self.assertTrue(any(c[0] == 'assets' for c in self.client.calls[places[0]+1:places[1]]))

    def test_failed_reconciliation_never_retries_mutation(self):
        self.client.upload_after = 1; self.client.fail_reconcile = True
        with self.assertRaises(g.UncertainMutation): self.sink.put_part(*self.part())
        self.assertEqual(sum(c[0] == 'upload' for c in self.client.calls), 1)

    def test_incomplete_or_duplicate_asset_refuses_overwrite(self):
        p, spec = self.part()
        self.client.add(spec['name'], b'', state='starter')
        with self.assertRaises(g.Conflict): self.sink.put_part(p, spec)
        self.client.add(spec['name'], b'PART')
        with self.assertRaises(g.Conflict): self.sink.open_part(spec['name'])
        self.assertFalse(any(c[0] == 'upload' for c in self.client.calls))

    def test_manifest_staged_read_before_atomic_final_rename(self):
        p, spec = self.manifest(); self.sink.commit_manifest(p, spec)
        calls = self.client.calls
        up = next(i for i,c in enumerate(calls) if c[0] == 'upload')
        rename = next(i for i,c in enumerate(calls) if c[0] == 'rename')
        self.assertIn('.staging.json', calls[up][1])
        self.assertTrue(any(c[0] == 'read' for c in calls[up+1:rename]))
        self.assertEqual(self.client.items[0]['name'], 'cache.json')
        with self.sink.open_manifest() as stream: self.assertEqual(stream.read(), p.read_bytes())
        self.assertEqual(len(list(self.root.glob('.gh-release-*'))), 0)

    def test_corrupt_staging_never_exposes_manifest(self):
        self.client.corrupt_stage = True
        with self.assertRaises(g.Conflict): self.sink.commit_manifest(*self.manifest())
        self.assertFalse(any(x['name'] == 'cache.json' for x in self.client.items))
        self.assertFalse(any(c[0] == 'rename' for c in self.client.calls))

    def test_manifest_lost_rename_response_is_reconciled(self):
        self.client.rename_after = 1
        self.sink.commit_manifest(*self.manifest())
        self.assertEqual(sum(c[0] == 'rename' for c in self.client.calls), 1)

    def test_manifest_retry_reads_same_stage_before_second_rename(self):
        self.client.rename_before = 1
        self.sink.commit_manifest(*self.manifest())
        places = [i for i,c in enumerate(self.client.calls) if c[0] == 'rename']
        self.assertEqual(len(places), 2)
        self.assertTrue(any(c[0] == 'assets' for c in self.client.calls[places[0]+1:places[1]]))

    def test_canonical_conflict_or_race_never_clobbers(self):
        p, spec = self.manifest()
        self.client.add('cache.json', b'OTHER')
        with self.assertRaises(g.Conflict): self.sink.commit_manifest(p, spec)
        self.assertFalse(any(c[0] in ('upload','rename') for c in self.client.calls))
        self.client.items.clear()
        self.client.before_rename = lambda c: c.add('cache.json', b'OTHER')
        with self.assertRaises(g.Conflict): self.sink.commit_manifest(p, spec)
        self.assertEqual(next(x for x in self.client.items if x['name']=='cache.json')['data'], b'OTHER')

    def test_failed_rename_reconciliation_never_retries_or_deletes(self):
        self.client.rename_after = 1
        self.client.fail_rename_reconcile = True
        with self.assertRaises(g.UncertainMutation): self.sink.commit_manifest(*self.manifest())
        self.assertEqual(sum(c[0] == 'rename' for c in self.client.calls), 1)
        self.assertEqual(len(self.client.items), 1)
        self.assertEqual(self.client.items[0]['name'], 'cache.json')

    def test_missing_gh_startup_leaves_no_process_or_resource_warning(self):
        runner = g.GhRunner(str(self.root/'does-not-exist'))
        with self.assertRaises(FileNotFoundError): runner.run([])
        with self.assertRaises(ValueError): runner.open([], limit=-1)

    def test_equal_canonical_commit_is_read_only_idempotent(self):
        p, spec = self.manifest(); self.client.add('cache.json', p.read_bytes())
        self.sink.commit_manifest(p, spec)
        self.assertFalse(any(c[0] in ('upload','rename') for c in self.client.calls))

    def test_draft_changes_stop_before_mutation(self):
        self.client.release_data['draft'] = False
        with self.assertRaises(g.DraftRequired): self.sink.put_part(*self.part())
        self.assertFalse(self.client.items)

    def test_pagination_and_missing_objects(self):
        for i in range(100): self.client.add('dummy-'+str(i), b'')
        with self.assertRaises(FileNotFoundError): self.sink.open_manifest()
        self.assertTrue(any(c == ('assets', 2) for c in self.client.calls))
        with self.assertRaises(FileNotFoundError): self.sink.open_part('cache-000001.tar.zst.part')

    def test_actual_rolling_publisher_and_full_validator(self):
        sys.path.insert(0, str(HERE.parent))
        from test_rolling_cache import RollingTests
        import rolling_cache as rc
        f = RollingTests(); f.setUp()
        try:
            _, receipt = f.publish(self.sink)
            self.assertEqual(receipt['status'], 'complete')
            self.assertEqual(receipt['spool_peak_parts'], 1)
            check = f.base/'independent'; check.mkdir()
            manifest = rc.validate_sink(self.sink, receipt['manifest_sha256'], check)
            self.assertTrue(manifest['members'])
            self.assertEqual([c[0] for c in self.client.calls if c[0] in ('upload','rename')][-1], 'rename')
            self.assertEqual(sum(x['name']=='cache.json' for x in self.client.items), 1)
        finally: f.doCleanups()


class CliTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.state = self.root/'state.json'
        self.state.write_text(json.dumps({'release': {'id':7,'tag_name':'cache/test-1','draft':True},
                                         'assets':[], 'next_id':1, 'calls':[]}))
        self.env = dict(os.environ, MOCK_GH_STATE=str(self.state), GH_DEBUG='api')
        self.runner = g.GhRunner(str(HERE/'fake_gh.py'), env=self.env, timeout=10)
        self.client = g.GhClient(self.runner)

    def test_actual_fake_gh_cli_upload_readback_stage_patch_and_ambiguous_response(self):
        data=json.loads(self.state.read_text());data['upload_after_error']=True;data['rename_after_error']=True
        self.state.write_text(json.dumps(data))
        s=g.GitHubReleaseSink('o/r','cache/test-1',client=self.client)
        p=self.root/'blob';p.write_bytes(b'part')
        s.put_part(p,descriptor('cache-000000.tar.zst.part',b'part'))
        p.write_bytes(b'{"v":1}')
        s.commit_manifest(p,descriptor('cache.json',p.read_bytes()))
        with s.open_manifest() as stream:self.assertEqual(stream.read(),p.read_bytes())
        calls=json.loads(self.state.read_text())['calls']
        self.assertEqual(sum('--method' in a and a[a.index('--method')+1]=='POST' for a in calls),2)
        self.assertEqual(sum('--method' in a and a[a.index('--method')+1]=='PATCH' for a in calls),1)
        self.assertFalse(any('--clobber' in a or 'DELETE' in a or 'create' in a for a in calls))
        self.assertNotIn('GH_DEBUG',self.runner.env)

    def control(self, program, **kwargs):
        p=self.root/'control.py';p.write_text('#!/usr/bin/env python3\n'+program);p.chmod(0o700)
        return g.GhRunner(str(p), env=dict(os.environ), **kwargs)

    def test_stdout_and_stderr_bounds_and_nonzero_exit(self):
        r=self.control('import os\nos.write(1,b"x"*10000)\n',json_limit=100)
        with self.assertRaisesRegex(g.SinkError,'stdout exceeded'):r.run([])
        r=self.control('import os,sys\nos.write(2,b"s"*100000)\nsys.exit(2)\n')
        with self.assertRaises(g.GhFailure) as cm:r.run([])
        self.assertEqual(len(cm.exception.stderr),4096)
        self.assertNotIn('ssss',str(cm.exception))

    def test_timeout_partial_close_and_binary_overrun(self):
        r=self.control('import time\ntime.sleep(30)\n',timeout=.1)
        with self.assertRaisesRegex(g.SinkError,'timed out'):r.run([])
        r=self.control('import os,time\nos.write(1,b"abc")\ntime.sleep(30)\n',timeout=10)
        with r.open([],limit=3) as stream:
            self.assertEqual(stream.read(1),b'a');process=stream.process
        self.assertIsNotNone(process.poll())
        r=self.control('import os\nos.write(1,b"abcd")\n')
        with r.open([],limit=3) as stream:
            with self.assertRaisesRegex(g.SinkError,'stdout exceeded'):stream.read()

    def test_binary_reads_are_streamed(self):
        r=self.control('import os\nos.write(1,b"a"*200000)\n')
        with r.open([],limit=200000) as stream:
            count=0
            while data:=stream.read(17):
                self.assertLessEqual(len(data),17);count+=len(data)
            self.assertEqual(count,200000)


if __name__=='__main__':
    # Hard guard: no test may execute a real gh command even accidentally.
    original=subprocess.Popen
    def guarded(argv,*args,**kwargs):
        if Path(argv[0]).name=='gh':raise AssertionError('Real gh forbidden in tests')
        return original(argv,*args,**kwargs)
    with patch('subprocess.Popen',guarded):unittest.main(verbosity=2)
