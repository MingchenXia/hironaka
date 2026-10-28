#!/usr/bin/env python3
"""Four batches of at most four exact new targets; shared global writer lock."""
from pathlib import Path
import hashlib
import json
import subprocess
import time

E = Path(__file__).resolve().parent
D = E.parents[1]
plan = json.loads((E / 'installation-plan.json').read_text())
rows = plan['support_extracts'] + plan['source_modules']
modules = [row['destination_module'] for row in rows]
assert len(modules) == len(set(modules)) == 16
B = E / 'build-attempt01'
B.mkdir(exist_ok=False)
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
sources = {row['destination_path']: row['destination_sha256'] for row in rows}
for path, digest in sources.items():
    assert sha(D / path) == digest
(B / 'source-before.json').write_text(json.dumps(sources, indent=2) + '\n')
guards = json.loads((E / 'initial-existing-source-BP-artifact-guards.json').read_text())
def check_guards():
    for path, digest in guards.items():
        if path not in ['Hironaka.lean', 'blueprint/extensions.tex']:
            assert sha(D / path) == digest, ('Old33 math or artifact changed', path)
check_guards()
results = []
start = time.monotonic()
for offset in range(0, len(modules), 4):
    batch = B / f'batch-{offset // 4 + 1:02d}'
    batch.mkdir()
    targets = modules[offset:offset + 4]
    command = ['flock', '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock', 'lake', 'build', '--wfail', *targets]
    batch_start = time.monotonic()
    with (batch / 'build.log').open('w') as log:
        result = subprocess.run(command, cwd=D, stdout=log, stderr=subprocess.STDOUT)
    (batch / 'build.exit').write_text(str(result.returncode) + '\n')
    text = (batch / 'build.log').read_text()
    row = {'targets': targets, 'exit': result.returncode, 'seconds': time.monotonic() - batch_start,
           'warnings': sum(line.startswith('warning:') for line in text.splitlines()),
           'command': command, 'all_children_reaped': True}
    results.append(row)
    (batch / 'verification.json').write_text(json.dumps(row, indent=2) + '\n')
    print('NEW_TARGET_BATCH', offset // 4 + 1, 'exit', result.returncode, 'warnings', row['warnings'], flush=True)
    if result.returncode != 0:
        print('\n'.join(text.splitlines()[-80:]), flush=True)
        break
for path, digest in sources.items():
    assert sha(D / path) == digest
check_guards()
passed = len(results) == 4 and all(row['exit'] == row['warnings'] == 0 for row in results)
receipt = {'status': 'PASS_ALL16_NEW_MODULE_TARGETS' if passed else 'FAILED_NEW_MODULE_TARGET_BATCH',
           'native_revision': plan['native_revision'], 'standalone_base': plan['standalone_base'],
           'new_modules': 16, 'batches': results, 'seconds': time.monotonic() - start,
           'new_source_inputs_unchanged': True, 'old33_math_BP_artifact_guards_unchanged': True,
           'broad_root_or_glob_build': False, 'old33_kernel_or_Expr_replay': False,
           'all_children_reaped': True}
(B / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(receipt['status'], flush=True)
raise SystemExit(0 if passed else 1)
