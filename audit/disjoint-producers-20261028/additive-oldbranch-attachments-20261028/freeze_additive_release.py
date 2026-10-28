#!/usr/bin/env python3
"""Freeze two new whole modules; reuse unchanged 31-module evidence."""
from pathlib import Path
import hashlib
import json

E = Path(__file__).resolve().parent
A = E.parent
D = A.parents[1]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
plan = json.loads((E / 'plan.json').read_text())
old_plan = json.loads((A / 'plan.json').read_text())
old_freeze = json.loads((A / 'public31-release-freeze-final.json').read_text())
output = E / 'final-additive2-freeze.json'
assert not output.exists(), 'Freeze evidence is append-only'
assert sha(A / 'plan.json') == plan['original31_plan_sha256']
assert sha(A / 'independent/verified31-pairs.json') == plan['original31_receipt_sha256']
assert sha(D / 'Hironaka.lean') == plan['root_after_sha256']

# Preserve the real 31-module umbrella before state, including its full
# compiled output, instead of claiming that current root imports are unchanged.
before_rows = plan['cohort31_before_states']
before_paths = {row['path'] for row in before_rows}
for row in before_rows:
    assert sha(E / row['capture']) == row['sha256'], row['capture']
for path, row in old_freeze['all_source_BP_root_master_compiled_input_pins'].items():
    if path not in before_paths:
        assert sha(D / path) == row['sha256'], path
for row in old_freeze['sources']:
    assert sha(D / row['source_path']) == row['source_sha256']
    for path, digest in row['all_compiled_parts'].items():
        assert sha(D / path) == digest, path
for path, digest in old_plan['old_file_guards'].items():
    assert sha(D / path) == digest, path

build = json.loads((E / 'build-attempt01/verification.json').read_text())
expr = json.loads((E / 'full-expressions-attempt01/verification.json').read_text())
assert build['status'] == 'PASS_NEW2_MODULE_BUILD' and build['exit'] == build['warnings'] == 0
assert expr['status'] == 'PASS_ALL2_WHOLE_TYPES_VALUES_PROOFS'
assert not expr['numeric_or_proof_name_rewrites']
for path, digest in json.loads((E / 'full-expressions-attempt01/before-inputs.json').read_text()).items():
    assert sha(Path(path)) == digest, path
for row in expr['comparisons'].values():
    assert row['exit'] == 0 and row['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH'
    assert sha(E / row['report']) == row['sha256']
frontend_path = E / 'narrow-current-root-frontend.json'
frontend = json.loads(frontend_path.read_text())
assert frontend.get('exit') == 0, frontend
assert sha(D / '.lake/build/lib/lean/Hironaka.olean') != next(row['sha256'] for row in before_rows if row['path'] == '.lake/build/lib/lean/Hironaka.olean')
assert sha(D / plan['existing_whole_original_BP']) == plan['existing_whole_BP_sha256']

sources = []
input_paths = {D / 'Hironaka.lean', D / 'blueprint/extensions.tex', D / plan['existing_whole_original_BP'], E / 'plan.json', A / 'plan.json', frontend_path}
for row in plan['whole_modules']:
    source = D / row['destination_path']
    assert sha(source) == row['destination_sha256']
    input_paths.add(source)
    input_paths.add(E / row['raw_capture'])
    input_paths.add(E / row['draft_capture'])
    relative = Path(*row['destination_module'].split('.'))
    artifacts = {}
    for sub in ['lib/lean', 'ir']:
        base = D / '.lake/build' / sub / relative
        for path in sorted(base.parent.glob(base.name + '.*')):
            assert path.is_file()
            artifacts[str(path.relative_to(D))] = sha(path)
            input_paths.add(path)
    assert str(Path('.lake/build/lib/lean') / relative.with_suffix('.olean')) in artifacts
    sources.append({'module': row['destination_module'], 'source_path': row['destination_path'], 'source_sha256': row['destination_sha256'], 'all_compiled_parts': artifacts})
for sub in ['lib/lean', 'ir']:
    base = D / '.lake/build' / sub / 'Hironaka'
    input_paths.update(path for path in base.parent.glob(base.name + '.*') if path.is_file())
for row in before_rows:
    input_paths.add(E / row['capture'])

result = {
    'status': 'FROZEN_ADDITIVE2_AWAITING_UNIQUE_INDEPENDENT_PAIRS_AND_209_VISIBILITY',
    'native_revision': plan['native_revision'],
    'old31_pair_receipt': {'path': '../independent/verified31-pairs.json', 'sha256': sha(A / 'independent/verified31-pairs.json')},
    'old31_plan_sha256': sha(A / 'plan.json'),
    'old31_math_source_and_all_artifact_parts_unchanged': True,
    'old31_root_before_states_preserved': before_rows,
    'new_whole_modules': 2, 'new_physical_roots': 19,
    'publication_modules': 33, 'publication_whole_modules': 29, 'publication_support_files': 4,
    'publication_physical_roots': 748, 'publication_literal_bindings': 209,
    'publication_written_proofs': 100,
    'existing_whole_BP_unchanged': True,
    'new_BP_bindings_or_proofs_added': 0,
    'missing8_original_attachments_filled_by_complete_original_modules': True,
    'whole_source_type_proof_payload_changes': 0,
    'old_guard_files_unchanged': len(old_plan['old_file_guards']),
    'strict_full_types_values_proofs': expr['comparisons'],
    'narrow_root_frontend_owner': '/root',
    'narrow_root_frontend_receipt': {'path': 'narrow-current-root-frontend.json', 'sha256': sha(frontend_path)},
    'sources': sources,
    'current_source_BP_root_master_all_compiled_input_pins': {str(path.relative_to(D)): {'sha256': sha(path), 'bytes': path.stat().st_size} for path in sorted(input_paths)},
    'old31_kernel_or_Expr_replay': False,
    'merge_authorized': False,
}
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['old31_root_before_states_preserved', 'sources', 'current_source_BP_root_master_all_compiled_input_pins', 'strict_full_types_values_proofs']}, indent=2))
print('FINAL_ADDITIVE_FREEZE_SHA256', sha(output))
