"""Pin every whole-module and every actual support-root comparison input."""
from pathlib import Path
import hashlib, json, subprocess, sys

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
SOURCE = Path('/workspace/archon-nakamaye-main')
NATIVE = Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
REV = 'bae7068afc70d624cd8563fd4291436195a7f25f'
sha = lambda data: hashlib.sha256(data).hexdigest()
sys.path.insert(0, str(ROOT / 'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
whole = json.loads((A / 'provenance.json').read_text())
assert len(whole) == 57
support = json.loads((A / 'original-major-support-provenance.json').read_text())
stalk = json.loads((A / 'stalk-support-provenance.json').read_text())
support.append({'source_parent_module': stalk['source_module'],
                'source_parent_path': stalk['source_path'],
                'source_parent_sha256': stalk['source_parent_sha256'],
                'destination_module': stalk['destination_module'],
                'destination_path': stalk['destination_path'],
                'destination_sha256': stalk['destination_sha256']})
repair = ROOT / 'audit/actual-point-bennett-major-reproducibility-20261018'
old = json.loads((repair / 'original-support-source-provenance.json').read_text())
support.append(old)
assert len(support) == 7
assert len({r['source_parent_module'] for r in support}) == 7
assert len({r['destination_module'] for r in support}) == 7

snapshots = []
for family, records in [('whole', whole), ('support', support)]:
    for rec in records:
        module = rec['source_module'] if family == 'whole' else rec['source_parent_module']
        path = rec['source_path'] if family == 'whole' else rec['source_parent_path']
        expected = rec['source_sha256'] if family == 'whole' else rec['source_parent_sha256']
        raw = subprocess.check_output(['git', '-C', str(SOURCE), 'show', REV + ':' + path])
        assert sha(raw) == expected, module
        assert (NATIVE / (module.replace('.', '/') + '.lean')).read_bytes() == raw, module
        assert sha((ROOT / rec['destination_path']).read_bytes()) == rec['destination_sha256']
        native = NATIVE / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
        public = ROOT / '.lake/build/lib/lean' / (rec['destination_module'].replace('.', '/') + '.olean')
        assert native.is_file() and public.is_file()
        snapshots.append({'family': family, 'native_module': module,
                          'native_source_sha256': expected, 'native_olean_sha256': sha(native.read_bytes()),
                          'public_module': rec['destination_module'],
                          'public_source_sha256': rec['destination_sha256'],
                          'public_olean_sha256': sha(public.read_bytes())})
(A / 'strict-capture-source-and-kernel-snapshot.json').write_text(json.dumps(snapshots, indent=2) + '\n')
(A / 'old-modules.tsv').write_text(''.join(r['source_module'] + '\t' + r['destination_module'] + '\n' for r in whole))
(A / 'new-modules.tsv').write_text(''.join(r['destination_module'] + '\t' + r['destination_module'] + '\n' for r in whole))
(A / 'fragment-old-modules.tsv').write_text(''.join(r['source_parent_module'] + '\t' + r['destination_module'] + '\n' for r in support))
(A / 'fragment-new-modules.tsv').write_text(''.join(r['destination_module'] + '\t' + r['destination_module'] + '\n' for r in support))
paths = subprocess.check_output(['git', '-C', str(SOURCE), 'ls-tree', '-r', '--name-only', REV,
                                 '--', 'TranscendentalNakamaye/TranscendentalNakamaye'], text=True).splitlines()
modules = [p.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/', '.')
           for p in paths if p.endswith('.lean')]
normal = {m: names.new_mod(m) for m in modules
          if m.startswith(('TranscendentalNakamaye.FirstPass.', 'TranscendentalNakamaye.Pending.'))}
# These original modules have no earlier complete standalone module; their
# complete original prerequisites now live in the explicitly recorded support.
for r in support:
    if r['source_parent_module'].split('.')[-1] in [
            'HironakaActualFormalStandardMonomialHS', 'HironakaActualTranslatedInitialHS',
            'HironakaSmoothCentreRealDomainActualAmbientHS', 'HironakaOriginalGlobalPrincipalization']:
        normal[r['source_parent_module']] = r['destination_module']
(A / 'exact-module-renames.tsv').write_text(''.join(a + '\t' + b + '\n' for a, b in normal.items()))
fragment = dict(normal)
fragment.update({r['source_parent_module']: r['destination_module'] for r in support})
(A / 'fragment-exact-module-renames.tsv').write_text(''.join(a + '\t' + b + '\n' for a, b in fragment.items()))
profiles = {
    'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean': '1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755',
    'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean': '49aba8c3a923533a210946026b6ac67556c82e79d0c603b10c5b15994cf055ab',
    'audit/local-sharp-curves-20261015/compare_full_expr_dag.py': '28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063',
}
for path, digest in profiles.items():
    assert sha((ROOT / path).read_bytes()) == digest, path
(A / 'strict-frozen-tool-profiles.json').write_text(json.dumps(profiles, indent=2) + '\n')
print(json.dumps({'whole_modules': len(whole), 'support_modules': len(support),
                  'native_support_parent_roots_will_be_retained_complete': True,
                  'all_actual_public_support_roots_will_be_compared': True}))
