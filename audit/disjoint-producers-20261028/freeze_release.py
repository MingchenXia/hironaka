#!/usr/bin/env python3
"""Offline final publication freeze. No Lean, kernels, or Expr replay."""
from pathlib import Path
import collections
import hashlib
import json
import re

A = Path(__file__).resolve().parent
D = A.parents[1]
sha = lambda data: hashlib.sha256(data).hexdigest()
plan = json.loads((A / 'plan.json').read_text())
output = A / 'public31-release-freeze-final.json'
assert not output.exists(), 'Freeze evidence is append-only'
assert len(plan['source_modules']) == 27
assert len(plan['support_extracts']) == 4
assert len(plan['blueprints']) == 26

for path, digest in plan['old_file_guards'].items():
    assert sha((D / path).read_bytes()) == digest, path
for row in [*plan['source_modules'], *plan['support_extracts']]:
    assert sha((D / row['destination_path']).read_bytes()) == row['destination_sha256']
for row in [*plan['blueprints'], *plan['documentation_pointers']]:
    assert sha((D / row['destination_path']).read_bytes()) == row['destination_sha256']

# Assemble the final strict comparison roster without replaying any unchanged
# original or public captures. Keep each failed first attempt in its own path.
initial = json.loads((A / 'full-expressions-attempt01/verification.json').read_text())
owner = json.loads((A / 'full-expressions-owner-correction-attempt02/verification.json').read_text())
support = json.loads((A / 'support-full-expressions-attempt01/verification.json').read_text())
comparisons = dict(initial['comparisons'])
comparisons.update(owner['comparisons'])
for module, directory in [
    ('Hironaka.Resolution.HironakaDisjointControlledNormalPivot', 'full-expressions-pivot-public-attempt02'),
    ('Hironaka.Resolution.HironakaDisjointActualControlledSplit', 'full-expressions-actualsplit-public-attempt02'),
]:
    receipt_path = A / directory / 'verification.json'
    receipt = json.loads(receipt_path.read_text())
    assert receipt['status'] == 'PASS_REUSED_ORIGINAL_FULL_EXPR'
    assert receipt['compare_exit'] == receipt['export_exit'] == 0
    assert not receipt['numeric_or_proof_name_rewrites']
    for path, digest in receipt['source_artifact_inputs'].items():
        assert sha(Path(path).read_bytes()) == digest, path
    report = A / directory / 'comparison.json'
    check = json.loads(report.read_text())
    assert check['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH'
    comparisons[module] = {
        'exit': 0, 'status': check['status'],
        'report': str(report.relative_to(A)), 'sha256': sha(report.read_bytes()),
        'recapture_receipt': str(receipt_path.relative_to(A)),
    }
comparisons.update(support['comparisons'])
assert len(comparisons) == 31
for module, row in comparisons.items():
    assert row['exit'] == 0 and row['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH', module
    assert sha((A / row['report']).read_bytes()) == row['sha256']

seen = {}
def visit(path):
    path = path.resolve()
    if path in seen:
        return
    assert path.is_file(), str(path)
    text = path.read_text()
    seen[path] = text
    for name in re.findall(r'\\input\{([^}]+)\}', text):
        child = path.parent / name
        visit(child if child.suffix else child.with_suffix('.tex'))
visit(D / 'blueprint/extensions.tex')
label_paths = collections.defaultdict(list)
for path, text in seen.items():
    for label in re.findall(r'\\label\{([^}]+)\}', text):
        label_paths[label].append(str(path.relative_to(D)))
new_docs = [*plan['blueprints'], *plan['documentation_pointers']]
bindings = []
uses = []
references = []
new_labels = []
ready = 0
for row in new_docs:
    path = (D / row['destination_path']).resolve()
    assert path in seen
    text = seen[path]
    ready += text.count('\\leanok')
    new_labels.extend(re.findall(r'\\label\{([^}]+)\}', text))
    for group in re.findall(r'\\lean\{([^}]+)\}', text):
        bindings.extend(x.strip() for x in group.split(',') if x.strip())
    for group in re.findall(r'\\uses\{([^}]+)\}', text):
        uses.extend(x.strip() for x in group.split(',') if x.strip())
    references.extend(re.findall(r'\\(?:eqref|ref|autoref)\{([^}]+)\}', text))
missing = sorted(set([*uses, *references]) - set(label_paths))
duplicates = {label: label_paths[label] for label in new_labels if len(label_paths[label]) > 1}
assert not missing, missing
assert not duplicates, duplicates

sources = []
all_inputs = {
    'Hironaka.lean', 'blueprint/extensions.tex',
    str((A / 'plan.json').relative_to(D)),
}
all_inputs.update(row['destination_path'] for row in new_docs)
all_inputs.update(str(path.relative_to(D)) for path in seen)
for row in [*plan['source_modules'], *plan['support_extracts']]:
    module = row['destination_module']
    rel = Path(*module.split('.'))
    artifacts = {}
    for sub in ['lib/lean', 'ir']:
        base = D / '.lake/build' / sub / rel
        for path in sorted(base.parent.glob(base.name + '.*')):
            assert path.is_file()
            relative = str(path.relative_to(D))
            artifacts[relative] = sha(path.read_bytes())
            all_inputs.add(relative)
    assert str(Path('.lake/build/lib/lean') / rel.with_suffix('.olean')) in artifacts, module
    all_inputs.add(row['destination_path'])
    sources.append({
        'module': module, 'source_path': row['destination_path'],
        'source_sha256': row['destination_sha256'], 'all_compiled_parts': artifacts,
    })

old_freeze = json.loads((A / 'public31-source-kernel-freeze.json').read_text())
old_drift = []
for row in old_freeze['sources']:
    for path, digest in row['kernel_parts'].items():
        actual = sha((D / path).read_bytes())
        if actual != digest:
            old_drift.append({'module': row['module'], 'path': path, 'old_sha256': digest, 'current_sha256': actual})
assert len(old_drift) == 1
assert old_drift[0]['module'] == 'Hironaka.Resolution.HironakaDisjointActualControlledSplit'

rootlog = A / 'full-root-build.log'
rootexit = A / 'full-root-build.exit'
assert rootexit.read_text().strip() == '0'
diagnostic = {
    'inherited_broad_root_build': True,
    'producer_identity_or_original_command_not_established_from_retained_logs': True,
    'log': 'full-root-build.log', 'log_sha256': sha(rootlog.read_bytes()),
    'exit': 0, 'jobs_reported': 7363,
    'vendor_warning_observations': sum(line.startswith('warning:') for line in rootlog.read_text().splitlines()),
    'not_counted_as_clean_narrow_validation': True,
    'not_rerun_in_this_release_lane': True,
    'changed_old_freeze_artifacts': old_drift,
    'affected_module_public_only_strict_recapture': 'full-expressions-actualsplit-public-attempt02/verification.json',
    'raw_original_capture_replayed': False,
}
result = {
    'status': 'FROZEN31_FINAL_AWAITING_UNIQUE_INDEPENDENT_TARGET_PAIRS',
    'native_revision': plan['native_revision'], 'standalone_base': plan['standalone_base'],
    'plan_sha256': sha((A / 'plan.json').read_bytes()),
    'whole_source_modules': 27, 'complete_original_support_files': 4,
    'actual_new_physical_module_roster': 31,
    'whole_original_BP_chapters': 26,
    'complete_original_BP_proofs': sum(row['proofs'] for row in plan['blueprints']),
    'new_support_written_proofs': sum(row['proofs'] for row in plan['documentation_pointers']),
    'new_BP_inputs': len(new_docs), 'actual_master_input_files': len(seen),
    'literal_binding_observations': len(bindings), 'unique_literal_bindings': len(set(bindings)),
    'uses_observations': len(uses), 'references_observations': len(references),
    'unresolved_references': missing, 'duplicate_new_labels': duplicates,
    'inherited_native_ready_markers': ready,
    'target_ready_claim_waits_for_independent_pairs': True,
    'old_files_byte_preserved': len(plan['old_file_guards']),
    'all31_strict_full_types_values_proofs': comparisons,
    'sources': sources,
    'all_source_BP_root_master_compiled_input_pins': {
        path: {'sha256': sha((D / path).read_bytes()), 'bytes': (D / path).stat().st_size}
        for path in sorted(all_inputs)
    },
    'inherited_diagnostic': diagnostic,
    'author_compiler_or_kernel_or_expr_used_for_this_freeze': False,
    'all_unchanged_evidence_reused': True,
    'original_open_goals_changed': False,
    'merge_authorized': False,
}
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['sources', 'all_source_BP_root_master_compiled_input_pins', 'all31_strict_full_types_values_proofs']}, indent=2))
print('FINAL_FREEZE_SHA256', sha(output.read_bytes()))
