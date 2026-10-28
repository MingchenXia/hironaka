#!/usr/bin/env python3
"""Final new16 freeze after exact builds, strict Expr, and one root frontend."""
from pathlib import Path
import collections
import hashlib
import json
import re

E = Path(__file__).resolve().parent
D = E.parents[1]
A = D / 'audit/disjoint-producers-20261028'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
plan = json.loads((E / 'installation-plan.json').read_text())
baseline = json.loads((E / 'first33-publication/receipt.json').read_text())
output = E / 'final-new16-freeze.json'
assert not output.exists()
assert sha(D / 'Hironaka.lean') == plan['root_after_sha256']
assert sha(D / 'blueprint/extensions.tex') == plan['master_after_sha256']
assert json.loads((E / 'build-attempt01/verification.json').read_text())['status'] == 'PASS_ALL16_NEW_MODULE_TARGETS'
frontend = json.loads((E / 'narrow-current-root-frontend.json').read_text())
assert frontend['exit'] == frontend['warnings'] == 0
assert frontend['old33_math_source_BP_all_artifacts_unchanged']
assert frontend['new16_math_source_all_artifacts_unchanged']
assert json.loads((E / 'ordinary-import-visibility-final.json').read_text())['missing'] == []

comparisons = {}
physical_count = 0
for directory, count in [('full-expressions-whole-attempt01', 14), ('full-expressions-support-attempt01', 2)]:
    state = json.loads((E / directory / 'verification.json').read_text())
    assert state['status'] == f'PASS_ALL{count}_WHOLE_TYPES_VALUES_PROOFS'
    assert not state['defeq_or_alpha_or_numeric_erasure']
    assert state['public_root_filters'] == state['allowed_extras'] == 0
    for path, digest in json.loads((E / directory / 'before-inputs.json').read_text()).items():
        assert sha(Path(path)) == digest, path
    for module, row in state['comparisons'].items():
        assert row['exit'] == 0 and row['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH'
        assert sha(E / row['report']) == row['sha256']
        assert row['public_actual_roots'] == row['original_actual_roots']
        comparisons[module] = row
        physical_count += row['public_actual_roots']
assert len(comparisons) == 16 and physical_count == 230

guards = json.loads((E / 'initial-existing-source-BP-artifact-guards.json').read_text())
root_outputs = {row['path'] for row in baseline['captures'] if row['path'].startswith('.lake/')}
exceptions = root_outputs | {'Hironaka.lean', 'blueprint/extensions.tex'}
for path, digest in guards.items():
    if path not in exceptions:
        assert sha(D / path) == digest, ('Original33 math or BP artifact changed', path)
for row in baseline['captures']:
    assert sha(E / row['capture']) == row['sha256']

input_paths = {E / 'installation-plan.json', E / 'plan.json', E / 'support-extraction-plan.json',
               E / 'external-prerequisite-plan.json', E / 'narrow-current-root-frontend.json',
               E / 'ordinary-import-visibility-final.json', D / 'Hironaka.lean', D / 'blueprint/extensions.tex'}
sources = []
native_sources = []
N = Path(plan['native_source_checkout']) / 'TranscendentalNakamaye'
for row in plan['support_extracts'] + plan['source_modules']:
    source = D / row['destination_path']
    assert sha(source) == row['destination_sha256']
    input_paths.add(source)
    relative = Path(*row['destination_module'].split('.'))
    parts = {}
    for sub in ['lib/lean', 'ir']:
        base = D / '.lake/build' / sub / relative
        for path in base.parent.glob(base.name + '.*'):
            if path.is_file():
                parts[str(path.relative_to(D))] = sha(path)
                input_paths.add(path)
    assert str(Path('.lake/build/lib/lean') / relative.with_suffix('.olean')) in parts
    sources.append({'module': row['destination_module'], 'source_path': row['destination_path'],
                    'source_sha256': row['destination_sha256'], 'all_compiled_parts': parts})
    native_relative = Path(*row['source_module'].split('.'))
    native_parts = {str(N / native_relative.with_suffix('.lean')): sha(N / native_relative.with_suffix('.lean'))}
    for sub in ['lib/lean', 'ir']:
        base = N / '.lake/build' / sub / native_relative
        native_parts.update({str(path): sha(path) for path in base.parent.glob(base.name + '.*') if path.is_file()})
    native_sources.append({'native_module': row['source_module'], 'all_native_source_artifact_parts': native_parts})
for sub in ['lib/lean', 'ir']:
    base = D / '.lake/build' / sub / 'Hironaka'
    input_paths.update(path for path in base.parent.glob(base.name + '.*') if path.is_file())

seen = {}
def visit(path):
    path = path.resolve()
    if path in seen:
        return
    assert path.is_file(), str(path)
    text = path.read_text()
    seen[path] = text
    input_paths.add(path)
    for name in re.findall(r'\\input\{([^}]+)\}', text):
        child = path.parent / name
        visit(child if child.suffix else child.with_suffix('.tex'))
visit(D / 'blueprint/extensions.tex')
all_labels = collections.defaultdict(list)
for path, text in seen.items():
    for label in re.findall(r'\\label\{([^}]+)\}', text):
        all_labels[label].append(str(path.relative_to(D)))
new_bindings = []
new_labels = []
new_uses = []
new_written_proofs = 0
new_native_ready_markers = 0
for row in plan['whole_blueprints'] + plan['documentation_pointers']:
    path = (D / row['destination_path']).resolve()
    assert path in seen and sha(path) == row['destination_sha256']
    text = seen[path]
    new_written_proofs += text.count('\\begin{proof}')
    new_native_ready_markers += text.count('\\leanok')
    new_labels.extend(re.findall(r'\\label\{([^}]+)\}', text))
    for group in re.findall(r'\\lean\{([^}]+)\}', text):
        new_bindings.extend(name.strip() for name in group.split(',') if name.strip())
    for group in re.findall(r'\\uses\{([^}]+)\}', text):
        new_uses.extend(name.strip() for name in group.split(',') if name.strip())
missing = sorted(set(new_uses) - set(all_labels))
collisions = {label: all_labels[label] for label in new_labels if len(all_labels[label]) > 1}
assert not missing and not collisions
assert len(new_bindings) == len(set(new_bindings)) == 61
assert new_written_proofs == 32
assert len(seen) == 1039
for directory in ['raw-source', 'raw-blueprint', 'support-original-parents', 'original-support-blueprint-nodes',
                  'external-native-parents', 'external-native-nodes', 'first33-publication']:
    input_paths.update(path for path in (E / directory).rglob('*') if path.is_file())
for pattern in ['*.py', '*.lean']:
    input_paths.update((E / 'independent').glob(pattern))

result = {
    'status': 'FROZEN_NEW16_AWAITING_UNIQUE_INDEPENDENT_PAIRS_AND_270_BINDINGS',
    'native_revision': plan['native_revision'], 'standalone_base': plan['standalone_base'],
    'installation_plan_sha256': sha(E / 'installation-plan.json'),
    'new_modules': 16, 'new_whole_modules': 14, 'new_original_support_files': 2,
    'new_physical_declarations': physical_count, 'new_whole_BP_chapters': 12,
    'new_BP_inputs': 14, 'new_complete_whole_BP_proofs': 30, 'new_written_support_proofs': 2,
    'new_written_proofs': new_written_proofs, 'new_literal_bindings': new_bindings,
    'new_native_inherited_ready_markers': new_native_ready_markers,
    'new_local_support_ready_markers': 0,
    'new_label_count': len(new_labels), 'new_label_collisions': collisions,
    'new_uses_observations': len(new_uses), 'unresolved_uses': missing,
    'actual_master_input_files': len(seen),
    'composite_modules': 49, 'composite_whole_modules': 43, 'composite_support_files': 6,
    'composite_physical_declarations': 978, 'composite_literal_bindings': 270,
    'composite_written_proofs': 132,
    'original33_math_source_BP_and_all_artifact_parts_unchanged': True,
    'original33_nonumbrella_guard_paths_unchanged': len(guards) - len(exceptions),
    'original33_current_publication_and_root_before_states': 'first33-publication/',
    'changed_root_compiled_outputs_explicitly_preserved_and_authorized': frontend['authorized_root_output_changes'],
    'strict_full_types_values_proofs': comparisons,
    'sources': sources, 'native_reference_sources_and_all_parts': native_sources,
    'all_current_source_BP_root_master_compiled_and_static_audit_input_pins': {
        str(path.relative_to(D)): {'sha256': sha(path), 'bytes': path.stat().st_size} for path in sorted(input_paths)
    },
    'old33_kernel_or_Expr_replay': False,
    'full_project_build_claimed': False, 'original_goal_closure_changed': False,
    'merge_authorized': False,
}
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key: value for key, value in result.items() if key not in ['sources', 'native_reference_sources_and_all_parts', 'all_current_source_BP_root_master_compiled_and_static_audit_input_pins', 'strict_full_types_values_proofs', 'new_literal_bindings']}, indent=2))
print('FINAL_NEW16_FREEZE_SHA256', sha(output))
