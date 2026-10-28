#!/usr/bin/env python3
"""Inspect only actual physical CIs for the 14 newly planned source modules."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

E = Path(__file__).resolve().parent
D = E.parents[1]
A = D / 'audit/disjoint-producers-20261028'
plan = json.loads((E / 'plan.json').read_text())
N = Path(plan['native_source_checkout']) / 'TranscendentalNakamaye'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
paths = [A / 'ActualCalleePreflight.lean', E / 'plan.json', E / 'native-modules.txt', D / 'Hironaka.lean', D / '.lake/build/lib/lean/Hironaka.olean']
acceptance = {row['module']: row for row in plan['native_root_acceptance']}
for row in plan['source_modules']:
    relative = Path(*row['source_module'].split('.'))
    source = N / relative.with_suffix('.lean')
    artifact = N / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    assert sha(source) == row['source_sha256']
    assert artifact.is_file()
    if row['source_module'] in acceptance:
        assert sha(artifact) == acceptance[row['source_module']]['artifact_sha256']
    paths.extend([source, artifact])
guards = json.loads((E / 'initial-existing-source-BP-artifact-guards.json').read_text())
for path, digest in guards.items():
    assert sha(D / path) == digest, path
before = {str(path): sha(path) for path in paths}
B = E / 'callee-preflight-attempt01'
B.mkdir(exist_ok=False)
(B / 'before-pins.json').write_text(json.dumps(before, indent=2) + '\n')
command = [
    '/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh', 'flock', '-s',
    '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock',
    'lake', 'env', 'lean', '--run', str(A / 'ActualCalleePreflight.lean'),
    str(E / 'native-modules.txt'), str(B / 'actual-callees.json'),
]
start = time.monotonic()
with (B / 'probe.log').open('w') as log:
    result = subprocess.run(command, cwd=D, env=dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(N / '.lake/build/lib/lean')), stdout=log, stderr=subprocess.STDOUT)
(B / 'probe.exit').write_text(str(result.returncode) + '\n')
after = {str(path): sha(path) for path in paths}
(B / 'after-pins.json').write_text(json.dumps(after, indent=2) + '\n')
assert before == after
for path, digest in guards.items():
    assert sha(D / path) == digest, path
receipt = {
    'status': 'PASS_ACTUAL_METADATA_QUERY' if result.returncode == 0 else 'FAILED_ACTUAL_METADATA_QUERY',
    'exit': result.returncode, 'seconds': time.monotonic() - start, 'command': command,
    'native_revision': plan['native_revision'],
    'current_standalone_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=D, text=True).strip(),
    'new_whole_modules': 14, 'source_artifact_pins_unchanged': True,
    'existing_33_and_3678_guards_unchanged': len(guards), 'all_children_reaped': True,
    'public_source_root_BP_installed': False, 'kernel_or_fullExpr_or_old33_gate_replay': False,
}
(B / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
print((B / 'probe.log').read_text())
raise SystemExit(result.returncode)
