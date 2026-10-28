#!/usr/bin/env python3
"""The sole changed-source umbrella frontend for this new 16-module cohort."""
from pathlib import Path
import hashlib
import json
import subprocess
import time

E = Path(__file__).resolve().parent
D = E.parents[1]
plan = json.loads((E / 'installation-plan.json').read_text())
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
assert not (E / 'narrow-current-root-frontend.json').exists()
assert not (E / 'narrow-current-root-frontend.log').exists()
assert sha(D / 'Hironaka.lean') == plan['root_after_sha256']
assert sha(D / 'blueprint/extensions.tex') == plan['master_after_sha256']
for path, status in [('full-expressions-whole-attempt01/verification.json', 'PASS_ALL14_WHOLE_TYPES_VALUES_PROOFS'), ('full-expressions-support-attempt01/verification.json', 'PASS_ALL2_WHOLE_TYPES_VALUES_PROOFS')]:
    assert json.loads((E / path).read_text())['status'] == status
assert json.loads((E / 'build-attempt01/verification.json').read_text())['status'] == 'PASS_ALL16_NEW_MODULE_TARGETS'
baseline = json.loads((E / 'first33-publication/receipt.json').read_text())
guards = json.loads((E / 'initial-existing-source-BP-artifact-guards.json').read_text())
root_artifacts = {row['path'] for row in baseline['captures'] if row['path'].startswith('.lake/')}
exempt = root_artifacts | {'Hironaka.lean', 'blueprint/extensions.tex'}
def check_old33():
    for path, digest in guards.items():
        if path not in exempt:
            assert sha(D / path) == digest, ('Original33 math or BP artifact changed', path)
check_old33()
math_pins = {}
for row in plan['source_modules'] + plan['support_extracts']:
    assert sha(D / row['destination_path']) == row['destination_sha256']
    math_pins[row['destination_path']] = row['destination_sha256']
    relative = Path(*row['destination_module'].split('.'))
    for sub in ['lib/lean', 'ir']:
        base = D / '.lake/build' / sub / relative
        for path in base.parent.glob(base.name + '.*'):
            if path.is_file():
                math_pins[str(path.relative_to(D))] = sha(path)
before_root = {path: sha(D / path) for path in sorted(root_artifacts)}
(E / 'narrow-current-root-before-inputs.json').write_text(json.dumps({'new16_math_source_all_artifacts': math_pins, 'old33_umbrella_output_artifacts': before_root}, indent=2) + '\n')
command = ['flock', '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock',
           'lake', 'env', 'lean', '-o', '.lake/build/lib/lean/Hironaka.olean',
           '-i', '.lake/build/lib/lean/Hironaka.ilean', '-c', '.lake/build/ir/Hironaka.c', 'Hironaka.lean']
start = time.monotonic()
with (E / 'narrow-current-root-frontend.log').open('w') as log:
    result = subprocess.run(command, cwd=D, stdout=log, stderr=subprocess.STDOUT)
text = (E / 'narrow-current-root-frontend.log').read_text()
(E / 'narrow-current-root-frontend.exit').write_text(str(result.returncode) + '\n')
assert sha(D / 'Hironaka.lean') == plan['root_after_sha256']
for path, digest in math_pins.items():
    assert sha(D / path) == digest, ('New16 source or artifact changed while compiling umbrella', path)
check_old33()
after_root = {}
for sub in ['lib/lean', 'ir']:
    base = D / '.lake/build' / sub / 'Hironaka'
    after_root.update({str(path.relative_to(D)): sha(path) for path in base.parent.glob(base.name + '.*') if path.is_file()})
receipt = {
    'status': 'PASS_SINGLE_CHANGED_SOURCE_UMBRELLA_FRONTEND' if result.returncode == 0 else 'FAILED_CHANGED_SOURCE_UMBRELLA_FRONTEND',
    'exit': result.returncode, 'seconds': time.monotonic() - start,
    'warnings': sum(line.startswith('warning:') for line in text.splitlines()),
    'command': command, 'cwd': str(D), 'sole_owner': '/root/standalone_release_author',
    'root_source_sha256': plan['root_after_sha256'], 'source_unchanged': True,
    'old33_math_source_BP_all_artifacts_unchanged': True,
    'old33_root_output_before_states_preserved': 'first33-publication/',
    'authorized_root_output_changes': {path: {'before': before_root.get(path), 'after': digest} for path, digest in after_root.items() if before_root.get(path) != digest},
    'all_current_root_artifacts': after_root,
    'new16_math_source_all_artifacts_unchanged': True,
    'all_children_reaped': True, 'broad_root_or_glob_Lake_build': False,
    'old33_kernel_or_Expr_replay': False,
}
(E / 'narrow-current-root-frontend.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
raise SystemExit(result.returncode)
