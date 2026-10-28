#!/usr/bin/env python3
"""Install only the independently reviewed new cohort and pure root appends."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

E = Path(__file__).resolve().parent
D = E.parents[1]
sha = lambda data: hashlib.sha256(data).hexdigest()
plan = json.loads((E / 'plan.json').read_text())
support = json.loads((E / 'support-extraction-plan.json').read_text())
external = json.loads((E / 'external-prerequisite-plan.json').read_text())
baseline = json.loads((E / 'first33-publication/receipt.json').read_text())
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=D, text=True).strip() == baseline['ordinary_git_commit']
assert not (E / 'installation-plan.json').exists()
for path, digest in json.loads((E / 'initial-existing-source-BP-artifact-guards.json').read_text()).items():
    assert sha((D / path).read_bytes()) == digest, path
closure = json.loads((E / 'support-callee-closure/recursive-ordinary-metadata-summary.json').read_text())
assert closure['ordinary_queue_closed'] and closure['additional_ordinary_helpers'] == 0
for path in ['independent/original14-full-static-review.json', 'independent/codim-support-drafts-static-review.json']:
    receipt = json.loads((E / path).read_text())
    assert str(receipt.get('status', '')).startswith('PASS'), receipt

support_modules = [row['destination_module'] for row in support['support_extracts']]
whole = []
leaf_names = {'HironakaDisjointFirstStepHistoricalAnchor', 'HironakaDisjointCanonicalHistoricalAnchor'}
source_outputs = {}
for original in plan['source_modules']:
    row = dict(original)
    original_output = (E / row['draft_capture']).read_bytes()
    assert sha(original_output) == row['destination_sha256']
    row['initial_synchronized_destination_sha256'] = row['destination_sha256']
    row['original_draft_capture'] = row['draft_capture']
    output = original_output
    if row['destination_module'].split('.')[-1] in leaf_names:
        text = output.decode()
        at = re.search(r'^import ', text, re.M).start()
        output = (text[:at] + ''.join('import ' + module + '\n' for module in support_modules) + text[at:]).encode()
        row['additional_pure_support_imports'] = support_modules
        row['destination_sha256'] = sha(output)
        row['draft_capture'] = 'draft-source-with-support-imports/' + Path(row['destination_path']).name
        draft = E / row['draft_capture']
        draft.parent.mkdir(exist_ok=True)
        assert not draft.exists()
        draft.write_bytes(output)
    assert not (D / row['destination_path']).exists(), row['destination_path']
    source_outputs[row['destination_path']] = output
    whole.append(row)
for row in support['support_extracts']:
    output = (E / row['draft_capture']).read_bytes()
    assert sha(output) == row['destination_sha256']
    assert not (D / row['destination_path']).exists(), row['destination_path']
    source_outputs[row['destination_path']] = output

bp_outputs = {}
bp_rows = []
for row in plan['whole_blueprints']:
    output = (E / row['draft_capture']).read_bytes()
    assert sha(output) == row['destination_sha256']
    bp_outputs[row['destination_path']] = output
    bp_rows.append(row)
supplement = dict(support['local_written_BP_supplement'])
supplement['destination_sha256'] = supplement['draft_sha256']
bp_outputs[supplement['destination_path']] = (E / supplement['draft_capture']).read_bytes()
external_row = {'kind': 'honest_original_external_reference_index',
                'destination_path': 'blueprint/' + Path(external['draft_capture']).name,
                'draft_capture': external['draft_capture'], 'destination_sha256': external['draft_sha256'],
                'complete_written_proofs': 0, 'literal_bindings': 0, 'ready_markers': 0}
bp_outputs[external_row['destination_path']] = (E / external_row['draft_capture']).read_bytes()
for path, output in bp_outputs.items():
    assert not (D / path).exists(), path
for row in [supplement, external_row]:
    assert sha(bp_outputs[row['destination_path']]) == row['destination_sha256']

before_root = (D / 'Hironaka.lean').read_text()
before_master = (D / 'blueprint/extensions.tex').read_text()
assert before_root == (E / 'first33-publication/Hironaka.lean').read_text()
assert before_master == (E / 'first33-publication/blueprint/extensions.tex').read_text()
modules = support['support_extracts'] + whole
at = before_root.index('/-!')
after_root = before_root[:at] + ''.join('import ' + row['destination_module'] + '\n' for row in modules) + '\n' + before_root[at:]
at = before_master.rindex('\\end{document}')
after_master = before_master[:at] + ''.join('\\input{' + Path(path).stem + '}\n' for path in bp_outputs) + before_master[at:]

# The complete source-facing BP is installed before its Lean source.
for path, output in bp_outputs.items():
    target = D / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(output)
for path, output in source_outputs.items():
    target = D / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(output)
(D / 'Hironaka.lean').write_text(after_root)
(D / 'blueprint/extensions.tex').write_text(after_master)

guards = json.loads((E / 'initial-existing-source-BP-artifact-guards.json').read_text())
for path, digest in guards.items():
    if path not in ['Hironaka.lean', 'blueprint/extensions.tex']:
        assert sha((D / path).read_bytes()) == digest, path
result = {
    'status': 'INSTALLED_NEW16_REVIEWED_SOURCES_AND14_BP_INPUTS',
    'standalone_base': baseline['ordinary_git_commit'],
    'native_revision': plan['native_revision'], 'native_source_checkout': plan['native_source_checkout'],
    'source_modules': whole, 'support_extracts': support['support_extracts'],
    'whole_blueprints': bp_rows, 'documentation_pointers': [supplement, external_row],
    'source_module_count': 16, 'whole_module_count': 14, 'original_support_files': 2,
    'whole_BP_chapters': 12, 'whole_BP_proofs': 30, 'local_support_written_proofs': 2,
    'new_BP_inputs': 14, 'literal_bindings': 61,
    'proof_or_type_payload_edits': 0,
    'old33_math_source_BP_and_all_artifacts_unchanged': True,
    'old33_guard_paths_preserved_except2_captured_root_master_appends': len(guards) - 2,
    'before_root_master_source_capture': 'first33-publication/',
    'root_after_sha256': sha(after_root.encode()), 'master_after_sha256': sha(after_master.encode()),
    'root_frontend_owner': '/root/standalone_release_author',
    'independent_new16_kernel_physical_owner': '/root/standalone_release_peer',
    'old33_kernel_or_Expr_replay': False,
    'merge_authorized': False,
}
(E / 'installation-plan.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key: value for key, value in result.items() if key not in ['source_modules', 'support_extracts', 'whole_blueprints', 'documentation_pointers']}, indent=2))
