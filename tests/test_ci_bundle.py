import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'scripts'), str(ROOT / 'cache_tools'),
               str(ROOT / 'cache_tools/github_release_adapter')]
import build_all as b
import install_lean as installer
import publish_cache as publisher
import rolling_cache as rc
import setup_sidecars as sc
from test_github_release_sink import FakeClient


def git(repo, *args):
    return subprocess.check_output(['git', '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                                    *args], cwd=repo, text=True, stderr=subprocess.DEVNULL).strip()


class BundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='hironaka-ci-fixture-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = self.root / 'source'
        self.project.mkdir()

    def source(self, name, text='def fixture : Nat := 0\n'):
        path = self.project / (name.replace('.', '/')+'.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def fixture_project(self):
        self.source('Hironaka', 'import Hironaka.A\n')
        self.source('Hironaka.A')
        self.source('Hironaka.Supplement', 'import Hironaka.A\n')
        (self.project / '.gitignore').write_text('.lake/\n')
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        (self.project / 'scripts').mkdir()
        (self.project / 'scripts/CheckAxioms.lean').write_text('-- fixture only\n')
        dep = self.project / '.lake/packages/mathlib'
        dep.mkdir(parents=True)
        (dep / '.gitignore').write_text('.lake/\n')
        (dep / 'README').write_text('fixture dependency\n')
        git(dep, 'init', '-q'); git(dep, 'add', '.'); git(dep, 'commit', '-qm', 'fixture')
        rev = git(dep, 'rev-parse', 'HEAD')
        (self.project / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages',
            'packages': [{'name': 'mathlib', 'type': 'git', 'rev': rev,
                          'url': 'https://github.com/leanprover-community/mathlib4'}]}))
        git(self.project, 'init', '-q'); git(self.project, 'add', '.'); git(self.project, 'commit', '-qm', 'fixture')
        sha = git(self.project, 'rev-parse', 'HEAD')
        prefix = self.root / 'toolchain'
        (prefix / 'bin').mkdir(parents=True)
        (prefix / 'lib/lean').mkdir(parents=True)
        (prefix / 'lib/lean/Init.olean').write_bytes(b'fixture-not-a-real-Lean-object')
        lean = prefix / 'bin/lean'
        lean.write_text('#!/usr/bin/env python3\nimport sys\nfrom pathlib import Path\n'
                        'print(Path(__file__).resolve().parents[1] if "--print-prefix" in sys.argv else "fixture Lean")\n')
        lean.chmod(0o755)
        lake = prefix / 'bin/lake'
        lake.write_text('''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
with open(os.environ['FIXTURE_COMMANDS'], 'a') as f: f.write(json.dumps(sys.argv[1:])+'\\n')
if os.environ.get('FIXTURE_FAIL') and sys.argv[1:2] == ['build'] and len(sys.argv) > 2: sys.exit(9)
if sys.argv[1:2] == ['build']:
    names = ['Hironaka.A', 'Hironaka'] if len(sys.argv) == 2 else [a[1:].split(':')[0] for a in sys.argv[2:]]
    for name in names:
        p=Path('.lake/build/lib/lean')/(name.replace('.', '/')+'.olean')
        p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(('fixture '+name).encode())
        s=Path('.lake/build/ir')/(name.replace('.', '/')+'.setup.json')
        s.parent.mkdir(parents=True,exist_ok=True); s.write_text(json.dumps({'fixture':name}))
''')
        lake.chmod(0o755)
        env = {'PATH': str(prefix / 'bin')+os.pathsep+os.environ['PATH'], 'SOURCE_REF': sha,
               'GITHUB_REPOSITORY': publisher.DESTINATION, 'FIXTURE_COMMANDS': str(self.root / 'commands.jsonl')}
        return env

    def test_graph_nested_comments_strings_and_every_physical_module(self):
        self.source('Hironaka', '/- outer /- import Hironaka.Fake -/ -/\nimport Hironaka.A\n')
        self.source('Hironaka.A', 'def s := "import Hironaka.Fake"\n')
        self.source('Hironaka.Z', 'public import Hironaka.A -- comment\n')
        ordered, hashes, graph = b.inventory(self.project, with_graph=True)
        self.assertEqual(set(ordered), {'Hironaka', 'Hironaka.A', 'Hironaka.Z'})
        self.assertLess(ordered.index('Hironaka.A'), ordered.index('Hironaka.Z'))
        self.assertEqual(graph['Hironaka'], {'Hironaka.A'})
        self.assertEqual(set(hashes), set(ordered))

    def test_graph_rejects_missing_and_cycles(self):
        self.source('Hironaka', 'import Hironaka.Missing\n')
        with self.assertRaisesRegex(ValueError, 'Missing local import'): b.inventory(self.project)
        self.source('Hironaka.Missing', 'import Hironaka\n')
        with self.assertRaisesRegex(ValueError, 'cycle'): b.inventory(self.project)

    def test_setup_checkpoint_preserves_objects_and_merges_exact_originals(self):
        ir = self.project / '.lake/build/ir'
        ir.mkdir(parents=True)
        (ir / 'a.setup.json').write_bytes(b'actual-setup-bytes')
        (ir / 'keep.c').write_bytes(b'C-untouched')
        state = self.root / 'state'; state.mkdir()
        triples = sc.checkpoint(self.project, ['.lake/build'], state)
        self.assertFalse((ir / 'a.setup.json').exists())
        self.assertEqual((ir / 'keep.c').read_bytes(), b'C-untouched')
        mount, archive, metadata, removed = rc.merger.batch(*[Path(v) for v in triples[0]])
        self.assertEqual(removed, {'a.setup.json'})
        self.assertEqual(metadata['files']['a.setup.json']['sha256'], hashlib.sha256(b'actual-setup-bytes').hexdigest())
        self.assertEqual(sc.checkpoint(self.project, ['.lake/build'], state), triples)

    def test_setup_rejects_link_without_deleting_target(self):
        ir = self.project / '.lake/build/ir'; ir.mkdir(parents=True)
        target = self.root / 'outside'; target.write_bytes(b'preserve')
        (ir / 'bad.setup.json').symlink_to(target)
        state = self.root / 'state'; state.mkdir()
        with self.assertRaises(ValueError): sc.checkpoint(self.project, ['.lake/build'], state)
        self.assertEqual(target.read_bytes(), b'preserve')

    def test_disk_guard_uses_measured_capacity(self):
        with patch.object(b.shutil, 'disk_usage', return_value=shutil._ntuple_diskusage(10, 9, 1)):
            with self.assertRaisesRegex(RuntimeError, 'measured 1 bytes'): b.require_space(self.root, 2)

    def test_exact_source_gate_rejects_dirty_or_wrong_sha(self):
        env = self.fixture_project()
        b.check_source(self.project, env['SOURCE_REF'])
        with self.assertRaises(ValueError): b.check_source(self.project, '0'*40)
        (self.project / 'Hironaka.lean').write_text('-- changed\n')
        with self.assertRaises(ValueError): b.check_source(self.project, env['SOURCE_REF'])

    def test_full_fixture_build_then_actual_rolling_and_draft_adapter(self):
        env = self.fixture_project(); state = self.root / 'state'
        with patch.dict(os.environ, env), patch.object(b, 'require_space', return_value=50*1024**3):
            receipt = b.build(self.project, state, budget_minutes=1, batch_size=32)
        self.assertEqual(receipt['status'], 'complete')
        self.assertEqual(receipt['physical_module_count'], 3)
        self.assertEqual(receipt['supplemental_batches'], [['Hironaka.Supplement']])
        calls = [json.loads(x) for x in (self.root / 'commands.jsonl').read_text().splitlines()]
        self.assertEqual(calls, [['exe','cache','get'], ['exe','cache','clean!'], ['build'],
                                 ['build','+Hironaka.Supplement:olean']])
        client = FakeClient()
        with patch.dict(os.environ, env), patch.object(publisher, 'require_space', return_value=50*1024**3):
            result = publisher.publish(self.project, state, 'cache/test-1', client=client)
        self.assertEqual(result['status'], 'complete')
        self.assertEqual([x['name'] for x in client.items][-1], 'cache.json')
        sink = publisher.GitHubReleaseSink(publisher.DESTINATION, 'cache/test-1', client=client)
        check = self.root / 'extra-verify'; check.mkdir()
        manifest = rc.validate_sink(sink, result['manifest_sha256'], check)
        self.assertEqual(manifest['identity']['source_commit'], env['SOURCE_REF'])
        members = manifest['members']
        self.assertIn('.lake/build/ir/Hironaka/Supplement.setup.json', members)
        self.assertFalse(list((state / 'spool').glob('cache-*.part')))
        # Actual unchanged vendor restore, not an extraction imitation. Fixture
        # bytes are deliberately not compiled Lean; no native replay claimed.
        downloaded = self.root / 'downloaded'; downloaded.mkdir()
        for asset in client.items:
            (downloaded / asset['name']).write_bytes(asset['data'])
        for root in manifest['identity']['roots']:
            shutil.rmtree(self.project / root)
        with patch.dict(os.environ, env):
            rc.merger.verify(downloaded)
            import cache as original_cache
            original_cache.restore(self.project, Path(shutil.which('lean')), downloaded)
        self.assertEqual((self.project/'.lake/build/lib/lean/Hironaka/Supplement.olean').read_bytes(),
                         b'fixture Hironaka.Supplement')
        self.assertEqual(json.loads((self.project/'.lake/build/ir/Hironaka/Supplement.setup.json').read_text()),
                         {'fixture':'Hironaka.Supplement'})

    def test_failed_supplemental_build_has_incomplete_receipt_and_cannot_publish(self):
        env = self.fixture_project(); env['FIXTURE_FAIL'] = '1'; state = self.root / 'state'
        with patch.dict(os.environ, env), patch.object(b, 'require_space', return_value=50*1024**3):
            with self.assertRaisesRegex(RuntimeError, 'build-00000 failed'): b.build(self.project, state, 1)
            self.assertEqual(json.loads((state/'build-receipt.json').read_text())['status'], 'incomplete')
            client = FakeClient()
            with self.assertRaisesRegex(ValueError, 'Incomplete'): publisher.publish(self.project, state, 'cache/test-1', client=client)
            self.assertEqual(client.calls, [])

    def test_installer_digest_required_no_download_without_it(self):
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        metadata = {'tag_name':'v4.33.1', 'draft':False, 'assets':[{'name':'lean-4.33.1-linux.tar.zst'}]}
        calls = []
        def opener(url):
            calls.append(url); return io.BytesIO(json.dumps(metadata).encode())
        with self.assertRaisesRegex(ValueError, 'SHA256'): installer.install(self.project, self.root/'lean', opener)
        self.assertEqual(len(calls), 1)
        self.assertFalse((self.root/'lean').exists())

    def test_installer_full_verified_fixture_archive_and_version(self):
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        raw = io.BytesIO()
        script = b'#!/bin/sh\necho "Lean (version 4.33.1, fixture only)"\n'
        with tarfile.open(fileobj=raw, mode='w') as tar:
            directory = tarfile.TarInfo('lean-4.33.1-linux'); directory.type=tarfile.DIRTYPE; directory.mode=0o755
            tar.addfile(directory)
            entry = tarfile.TarInfo('lean-4.33.1-linux/bin/lean'); entry.size=len(script); entry.mode=0o755
            tar.addfile(entry, io.BytesIO(script))
        archive = subprocess.run(['zstd','-q','-c'],input=raw.getvalue(),capture_output=True,check=True).stdout
        url = 'https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst'
        metadata = {'tag_name':'v4.33.1','draft':False,'assets':[{'id':1,'name':'lean-4.33.1-linux.tar.zst',
            'digest':'sha256:'+hashlib.sha256(archive).hexdigest(),'size':len(archive),'browser_download_url':url}]}
        def opener(target): return io.BytesIO(archive if target==url else json.dumps(metadata).encode())
        with patch.dict(os.environ, {'GITHUB_PATH':str(self.root/'path')}):
            prefix = installer.install(self.project, self.root/'lean', opener)
        self.assertTrue((prefix/'bin/lean').is_file())
        self.assertFalse((self.root/'lean/lean-4.33.1-linux.tar.zst').exists())

    def test_workflow_scope_permissions_and_immutable_action_pins(self):
        import yaml
        # YAML1.1 treats 'on' as Boolean; BaseLoader preserves Actions key text.
        workflow = yaml.load((ROOT/'.github/workflows/build-cache.yml').read_text(), Loader=yaml.BaseLoader)
        self.assertEqual(workflow['on']['push']['branches'], ['hironaka-build-cache'])
        self.assertEqual(workflow['permissions'], {})
        job = workflow['jobs']['build']
        self.assertEqual(job['permissions'], {'contents':'write'})
        self.assertEqual(job['env']['LEAN_NUM_THREADS'], '3')
        for step in job['steps']:
            if 'uses' in step:
                self.assertRegex(step['uses'], r'@[0-9a-f]{40}$')
        self.assertEqual(job['env']['SOURCE_REF'],
                         '19a3232088fce3dab71eb2e2135d82683962c091')


if __name__ == '__main__': unittest.main()
