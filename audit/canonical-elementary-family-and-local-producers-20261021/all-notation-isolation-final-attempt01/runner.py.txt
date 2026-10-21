"""Run once on a stable export; retain an immutable actual typed witness."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
NATIVE = Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
RUNTIME = Path('/workspace/archon-nakamaye/work/lean-runtime')
NATIVE_LIB = NATIVE / '.lake/build/lib/lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


p = argparse.ArgumentParser()
p.add_argument('attempt', help='New immutable audit directory')
args = p.parse_args()
out = A / args.attempt
assert not out.exists()
assert (ROOT / '.lake/build/lib/lean/Hironaka.olean').is_file()
config_path = A / 'notation-frontend-owners-plan.json'
config = json.loads(config_path.read_text())
owners = config['owners']
expected = sum(x['notation_clauses'] * 3 for x in owners)
assert expected == config['expected_public_frontend_definitions'] == 60
assert 2 * expected == config['expected_original_and_public_frontend_definitions']
sources = sorted([ROOT / 'Hironaka.lean', *(ROOT / 'Hironaka').rglob('*.lean')])
fingerprints = {str(x.relative_to(ROOT)): sha(x) for x in sources}
base_paths = subprocess.check_output(
    ['git', 'ls-tree', '-r', '--name-only', config['frozen_standalone_base'], '--', 'Hironaka'],
    cwd=ROOT, text=True).splitlines()
old_sources = {x for x in base_paths if x.endswith('.lean')}
assert len(old_sources) == config['expected_old_physical_modules']
assert old_sources <= set(fingerprints)
new_sources = sorted(set(fingerprints) - old_sources - {'Hironaka.lean'})
assert len(new_sources) == config['expected_new_physical_modules']
new_modules = [x.removesuffix('.lean').replace('/', '.') for x in new_sources]
assert all('Hironaka.Resolution.' + x['short'] in new_modules for x in owners)
public_artifacts = {}
for name in new_modules + ['Hironaka']:
    path = ROOT / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
    public_artifacts[str(path)] = sha(path)
node_plan_path = A / 'blueprint-original-node-extract-plan.json'
node_plan = json.loads(node_plan_path.read_text())
upstream = sorted({name for spec in node_plan['extracts'].values()
                   for name in spec['separately_verified_original_bindings']})
assert len(upstream) == config['expected_upstream_only_names'] == 17
template_path = A / 'ParserLogicalIsolationAllNotationTemplate.lean'
template = template_path.read_text()
replacements = {
    '-- IMPORT_NATIVE_NOTATION_PARENTS': '\n'.join(
        'import TranscendentalNakamaye.Pending.' + x['short'] for x in owners),
    '-- PAIRS_EXPECTED_COUNTS': ',\n'.join(
        '    (`TranscendentalNakamaye.Pending.' + x['short'] +
        ', `Hironaka.Resolution.' + x['short'] + ', ' + str(x['notation_clauses']) + ')'
        for x in owners),
    '-- NEW_MODULE_NAMES': ',\n'.join('    `' + x for x in new_modules),
    '-- UPSTREAM_ONLY_NAMES': ',\n'.join('    `' + x for x in upstream),
    '-- EXPECTED_GENERATED_PUBLIC': '    ' + str(expected),
    '-- EXPECTED_WHOLE_MODULES': '    ' + str(len(sources)),
    '-- OUTPUT_JSON': '    ' + json.dumps(str(
        (out / 'all-notation-logical-isolation.json').relative_to(ROOT)))
}
for old, new in replacements.items():
    assert template.count(old) == 1, old
    template = template.replace(old, new)
native_inputs = {}
for x in owners:
    module = 'TranscendentalNakamaye/Pending/' + x['short']
    for path in [NATIVE / (module + '.lean'), NATIVE_LIB / (module + '.olean')]:
        native_inputs[str(path)] = sha(path)
out.mkdir()
probe = out / 'AllNotationLogicalIsolation.lean'
probe.write_text(template)
(out / 'runner.py.txt').write_bytes(Path(__file__).read_bytes())
(out / 'notation-plan.json').write_bytes(config_path.read_bytes())
(out / 'node-extract-plan.json').write_bytes(node_plan_path.read_bytes())
(out / 'source-inputs.json').write_text(json.dumps(fingerprints, indent=2) + '\n')
(out / 'native-inputs.json').write_text(json.dumps(native_inputs, indent=2) + '\n')
(out / 'public-artifacts.json').write_text(json.dumps(public_artifacts, indent=2) + '\n')
(out / 'new-physical-modules.json').write_text(json.dumps(new_modules, indent=2) + '\n')
controls = {str(config_path): sha(config_path), str(node_plan_path): sha(node_plan_path),
            str(template_path): sha(template_path), str(Path(__file__).resolve()): sha(Path(__file__))}
(out / 'control-inputs.json').write_text(json.dumps(controls, indent=2) + '\n')
env = dict(os.environ)
env['LEAN_PATH'] = str(NATIVE_LIB) + (':' + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
command = ['flock', '-s', str(RUNTIME / 'hironaka-standalone-build.lock'),
           str(RUNTIME / 'lean-probe.sh'), 'lake', 'env', 'lean', str(probe)]
with (out / 'probe.log').open('w') as log:
    proc = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
(out / 'probe.exit').write_text(str(proc.returncode) + '\n')
current = {str(x.relative_to(ROOT)) for x in
           [ROOT / 'Hironaka.lean', *(ROOT / 'Hironaka').rglob('*.lean')]}
unchanged = current == set(fingerprints) and all(
    sha(ROOT / name) == digest for name, digest in fingerprints.items())
unchanged = unchanged and all(sha(Path(name)) == digest for name, digest in
                              (native_inputs | public_artifacts | controls).items())
log_text = (out / 'probe.log').read_text()
clean_log = 'warning:' not in log_text and 'error:' not in log_text
result = {'status': 'PASS' if proc.returncode == 0 and unchanged and clean_log else 'BLOCKED',
          'exit': proc.returncode, 'whole_source_modules': len(sources),
          'new_physical_modules': len(new_modules), 'source_inputs_unchanged': unchanged,
          'native_and_control_inputs_unchanged': unchanged, 'command': command,
          'no_warning_or_error_diagnostics': clean_log, 'single_fair_reader': True,
          'public_artifacts_protected_by_shared_build_lock': True,
          'expected_typed_public_frontend_definitions': expected,
          'parser_body_structural_equality_claimed': False}
evidence_files = ['source-inputs.json', 'native-inputs.json', 'public-artifacts.json',
                  'control-inputs.json', 'new-physical-modules.json', 'notation-plan.json',
                  'node-extract-plan.json', 'runner.py.txt', 'AllNotationLogicalIsolation.lean',
                  'probe.exit', 'probe.log']
if (out / 'all-notation-logical-isolation.json').is_file():
    evidence_files.append('all-notation-logical-isolation.json')
result['evidence_sha256'] = {name: sha(out / name) for name in evidence_files}
(out / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result), flush=True)
assert proc.returncode == 0 and unchanged and clean_log
