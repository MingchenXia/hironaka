"""One immutable fair-reader run over the complete built public environment."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
RUNTIME = Path('/workspace/archon-nakamaye/work/lean-runtime')
NATIVE_LIB = Path('/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/build/lib/lean')

p = argparse.ArgumentParser()
p.add_argument('attempt')
args = p.parse_args()
out = A / args.attempt
assert not out.exists(), 'Each actual probe attempt is immutable.'
assert (ROOT / '.lake/build/lib/lean/Hironaka.olean').exists()
out.mkdir()
sources = sorted([ROOT / 'Hironaka.lean', *(ROOT / 'Hironaka').rglob('*.lean')])
fingerprints = {str(x.relative_to(ROOT)): hashlib.sha256(x.read_bytes()).hexdigest()
                for x in sources}
template = (A / 'ParserLogicalIsolationFinal.lean').read_text()
node_plan = json.loads((A / 'blueprint-original-node-extract-plan.json').read_text())
upstream_only = sorted({name for spec in node_plan['extracts'].values()
                        for name in spec['separately_verified_original_bindings']})
assert len(upstream_only) == 13
assert template.count('  let env ← getEnv\n') == 1
absence_guard = ('  let upstreamOnlyNames : Array Name := #[' +
                 ', '.join('`' + name for name in upstream_only) + ']\n' +
                 '  for name in upstreamOnlyNames do\n' +
                 '    unless (env.find? name).isNone do\n' +
                 '      throwError "Upstream-only blueprint binding is actually exported locally: {name}"\n')
template = template.replace('  let env ← getEnv\n', '  let env ← getEnv\n' + absence_guard)
json_anchor = '    ("parser_body_structural_equality_claimed",toJson false),'
assert template.count(json_anchor) == 1
template = template.replace(json_anchor,
    '    ("actual_upstream_only_public_names_verified_absent",toJson (upstreamOnlyNames.map Name.toString)),\n' +
    json_anchor)
assert template.count('unless moduleCount == 1476 ') == 1
template = template.replace('unless moduleCount == 1476 ',
                            f'unless moduleCount == {len(sources)} ')
old_output = 'audit/canonical-elementary-family-and-local-producers-20261021/parser-logical-isolation-final.json'
new_output = str((out / 'parser-logical-isolation-final.json').relative_to(ROOT))
assert template.count(old_output) == 1
template = template.replace(old_output, new_output)
probe = out / 'ParserLogicalIsolationFinal.lean'
probe.write_text(template)
(out / 'source-inputs.json').write_text(json.dumps(fingerprints, indent=2) + '\n')
(out / 'upstream-only-public-names.json').write_text(json.dumps(upstream_only, indent=2) + '\n')
(out / 'runner.py.txt').write_bytes(Path(__file__).read_bytes())
env = dict(os.environ)
env['LEAN_PATH'] = str(NATIVE_LIB) + (':' + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
command = ['flock', '-s', str(RUNTIME / 'hironaka-standalone-build.lock'),
           str(RUNTIME / 'lean-probe.sh'), 'lake', 'env', 'lean', str(probe)]
with (out / 'probe.log').open('w') as log:
    proc = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
(out / 'probe.exit').write_text(str(proc.returncode) + '\n')
current_sources = {str(x.relative_to(ROOT)) for x in
                   [ROOT / 'Hironaka.lean', *(ROOT / 'Hironaka').rglob('*.lean')]}
unchanged = current_sources == set(fingerprints) and all(
    hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
    for name, digest in fingerprints.items())
log_text = (out / 'probe.log').read_text()
clean_log = 'warning:' not in log_text and 'error:' not in log_text
report = {'status': 'PASS' if proc.returncode == 0 and unchanged and clean_log else 'BLOCKED',
          'exit': proc.returncode, 'whole_source_modules': len(sources),
          'source_inputs_unchanged': unchanged, 'command': command,
          'no_warning_or_error_diagnostics': clean_log,
          'native_search_path': str(NATIVE_LIB), 'single_fair_reader': True,
          'public_artifacts_protected_by_shared_build_lock': True,
          'parser_body_structural_equality_claimed': False}
(out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
assert proc.returncode == 0 and unchanged and clean_log
