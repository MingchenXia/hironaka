"""Freeze complete compiled imports and classify EVERY local module for replay.

This prepares a coverage inventory. Only the subsequent successful frozen
LeanChecker run can certify the modules assigned to fresh replay.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

from validate_previous_reuse import module_parts, validate_reuse

here = Path(__file__).resolve().parent
root = here.parents[1]
previous = here.parent / 'local-coefficients-and-curve-overlaps-20261015'
subprocess.run([sys.executable, str(here / 'snapshot_kernel_artifacts.py'),
                str(here / 'kernel-artifacts-before.json')], cwd=root, check=True)
before = json.loads((here / 'kernel-artifacts-before.json').read_text())
old_raw = (previous / 'kernel-artifacts-after.json').read_bytes()
old = json.loads(old_raw)
paths = {source.removesuffix('.lean').replace('/', '.'): source
         for source in before['sources'] if source != 'Hironaka.lean'}
old_modules = {source.removesuffix('.lean').replace('/', '.')
               for source in old['sources'] if source != 'Hironaka.lean'}
new_modules = set(json.loads((here / 'new-module-targets.json').read_text()))
affected = {'Hironaka.Analytic.GeometricPureDimension'}
while True:
    extended = affected | {module for module in paths
        if set(before['actual_compiler_direct_imports'][module]) & affected}
    if extended == affected:
        break
    affected = extended
fresh_old = old_modules & affected
additional = []
reused = []
for module in sorted(old_modules - affected):
    assert before['sources'][paths[module]] == old['sources'][paths[module]]
    if module_parts(before['compiled_kernel_data_parts'], module) == module_parts(old['compiled_kernel_data_parts'], module):
        reused.append(module)
    else:
        additional.append(module)
targets = sorted(new_modules | fresh_old | set(additional))
(here / 'kernel-modules.json').write_text(json.dumps(targets, indent=2) + '\n')
guard = {'status': 'PASS_PINNED_PREDECESSOR_REUSE_OUTSIDE_ENTIRE_REPAIR_CONE',
    'previous_public_main': '3aa1692af186967f63d4197a34114d6e316aed95',
    'previous_snapshot_sha256': hashlib.sha256(old_raw).hexdigest(),
    'previous_kernel_receipt_sha256': hashlib.sha256((previous / 'incremental-kernel-replay.json').read_bytes()).hexdigest(),
    'reused_nonroot_modules': len(reused), 'reused_exact_module_inventory': reused,
    'affected_preceding_modules_fresh_replay': sorted(fresh_old),
    'additional_changed_kernel_modules_fresh_replay': additional,
    'fresh_mathematical_module_inventory': targets,
    'every_repair_dependent_requires_fresh_replay_even_if_its_bytes_match': True,
    'actual_compiler_ilean_direct_imports_used': True,
    'root_requires_separate_fresh_replay': True,
    'fresh_replay_claimed_passed_here': False}
(here / 'previous-frozen-kernel-data-reuse.json').write_text(json.dumps(guard, indent=2) + '\n')
print(json.dumps(validate_reuse(here, before)))
