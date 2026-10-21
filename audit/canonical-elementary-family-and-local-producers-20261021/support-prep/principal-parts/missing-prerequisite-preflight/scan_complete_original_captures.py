"""Read-only missing-callee preflight over existing complete original captures.

The generated/private-name exclusions apply ONLY to this prerequisite search.
Every formal expression, kernel and axiom gate remains entirely unfiltered.
"""
from pathlib import Path
from collections import defaultdict
import gzip
import hashlib
import json

W = Path(__file__).resolve().parent
A = W.parents[2]
ROOT = A.parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def name_tree(tree):
    parts = []
    while tree[0] != 'anonymous':
        assert tree[0] in ['str', 'num'], tree
        parts.append(str(tree[2]))
        tree = tree[1]
    return '.'.join(reversed(parts))


def generated(name):
    return name.startswith('_private.') or any(s in name for s in
        ['.eq_', '.match_', '._proof_', '._simp_', '._aux_'])


def reachable(nodes, root):
    seen, stack = set(), [] if root is None else [root]
    while stack:
        index = stack.pop()
        if index in seen:
            continue
        seen.add(index)
        stack.extend(nodes[index]['children'])
    return seen


def main():
    old_warm = load(A / 'old-warm-actual-name-inventory.json')
    new = load(A / 'new-native-actual-name-inventory.json')
    old_full = load(W / 'old1159-actual-moduledata-names.json')
    native = load(W / 'native316-direct-callee-preflight.json')
    new_names = {r['canonical_public_name'] for m in new for r in m['actual_roots']}
    available_warm = new_names | {name for m in old_warm for name in m['actual_roots']}
    available = new_names | {name for m in old_full for name in m['actual_roots']}
    known = {
        'Hironaka.HolGerm.mk_sub\'', 'Hironaka.HolGerm.constHom_apply',
        'Hironaka.LocalGiraudTransform.regularAtDim_zeroSet',
        'Hironaka.StepOneWellFounded.lt_of_isCanonical_append',
        'Hironaka.StepOneWellFounded.lt_of_isCanonical_step',
        'Hironaka.SubmanifoldRestrictLe.restrictIdeal_le_of_restrictLe',
        'Hironaka.EmbeddedFromResolution.mem_maxLocus_iff_of_centresAvoid',
        'Hironaka.EmbeddedFromResolution.not_centresAvoid_of_cosupp_eq_empty',
    }
    files = sorted(p for p in A.rglob('*.jsonl.gz') if
                   'original' in p.name or 'native' in p.name)
    assert files
    frozen_files = [str(p.relative_to(A)) for p in files]
    rows = nodes_count = constant_nodes = eligible_nodes = excluded_generated = 0
    modules = set()
    baseline_absent = set()
    dependencies = defaultdict(set)
    complete = []
    incomplete = []
    for path in files:
        before = digest(path)
        local_rows = local_nodes = 0
        try:
            with gzip.open(path, 'rt') as stream:
                for line in stream:
                    assert line.endswith('\n'), 'Incomplete JSONL line'
                    row = json.loads(line)
                    assert 'fullExprNodes' in row and 'typeRoot' in row and 'valueRoot' in row
                    nodes = row['fullExprNodes']
                    local_rows += 1
                    local_nodes += len(nodes)
                    rows += 1
                    nodes_count += len(nodes)
                    modules.add(row['module'])
                    absent_nodes = {}
                    for index, node in enumerate(nodes):
                        if node['tag'] != 'constant':
                            continue
                        constant_nodes += 1
                        name = name_tree(node['data'][0])
                        if generated(name):
                            excluded_generated += 1
                            continue
                        if not name.startswith('Hironaka.'):
                            continue
                        eligible_nodes += 1
                        if name not in available_warm:
                            baseline_absent.add(name)
                        if name not in available:
                            absent_nodes[index] = name
                    if absent_nodes:
                        for field in ['typeRoot', 'valueRoot']:
                            used = reachable(nodes, row[field])
                            for index, name in absent_nodes.items():
                                if index in used:
                                    dependencies[name].add((row['module'], row['name'],
                                        'type' if field == 'typeRoot' else 'whole_value',
                                        str(path.relative_to(A))))
        except (EOFError, gzip.BadGzipFile, json.JSONDecodeError, AssertionError) as error:
            incomplete.append({'path': str(path.relative_to(A)), 'reason': str(error)})
            continue
        assert digest(path) == before, ('Original capture changed during read', path)
        complete.append({'path': str(path.relative_to(A)), 'sha256': before,
                         'complete_rows': local_rows, 'full_nodes': local_nodes})
    # Successful original captures must not be silently replaced by a partial
    # stream. A partial input is an explicit blocked diagnostic, never a PASS.
    assert not incomplete, incomplete
    actual = defaultdict(list)
    for occurrence in native['ordinary_missing_callee_occurrences']:
        actual[occurrence['canonical_dependency']].append(occurrence)
    combined = sorted(set(actual) | set(dependencies))
    missing = []
    for name in combined:
        missing.append({'canonical_dependency': name,
            'already_known_support': name in known,
            'all316_actual_direct_callee_occurrences': actual[name],
            'complete_raw_capture_callers': [{'parent_module': m, 'parent_declaration': d,
                'field': f, 'capture': p} for m,d,f,p in sorted(dependencies[name])]})
    provenance = load(A / 'provenance.json')
    expected_modules = {r['destination_module'] for r in provenance
                        if r['source_module'] in {r['source_module'] for r in new}}
    uncaptured = sorted(expected_modules - modules)
    report = {'status': 'BOUNDED_READ_ONLY_MISSING_PREREQUISITE_DIAGNOSTIC_NOT_A_PROOF_GATE',
        'old_warm_input_modules': len(old_warm),
        'old_complete_actual_metadata_modules': len(old_full),
        'old_complete_actual_metadata_roots': sum(len(r['actual_roots']) for r in old_full),
        'new_expected_parent_modules': len(new), 'new_expected_names': len(new_names),
        'all316_actual_direct_callee_inventory': native,
        'complete_original_capture_files_at_snapshot': len(complete),
        'complete_original_captured_modules': len(modules), 'captured_complete_rows': rows,
        'captured_full_DAG_nodes': nodes_count, 'constant_nodes_examined': constant_nodes,
        'eligible_Hironaka_constant_nodes': eligible_nodes,
        'generated_or_private_nodes_omitted_from_THIS_DIAGNOSTIC_ONLY': excluded_generated,
        'stale504_warm_union_absent_names': sorted(baseline_absent),
        'deducted_by_actual1159_metadata': sorted(baseline_absent - set(dependencies)),
        'missing_ordinary_names_combined': missing,
        'new_missing_names_after_known_support_deduction': [n for n in combined if n not in known],
        'known_support_names_observed_missing': [n for n in combined if n in known],
        'captured_raw_modules': sorted(modules), 'uncaptured_expected_new_modules': uncaptured,
        'uncaptured_parent_count': len(uncaptured),
        'full_Expr_or_kernel_or_axiom_gate_PASS_claimed': False,
        'uncaptured_parent_proof_payload_PASS_claimed': False,
        'formal_gate_roots_or_values_filtered': 0,
        'generated_names_normalized_or_erased_in_formal_gates': 0,
        'production_source_or_comparator_edits': 0, 'Expr_exports_or_kernel_replays_run': 0,
        'one_authorized_metadata_only_reader_run': True,
        'snapshot_all_existing_matching_paths': frozen_files,
        'complete_original_capture_inputs': complete,
        'incomplete_capture_inputs': incomplete,
        'files_created_after_snapshot_not_claimed_scanned': True,
        'evidence_sha256': {str(p.relative_to(A)): digest(p) for p in [
            A / 'old-warm-actual-name-inventory.json', A / 'new-native-actual-name-inventory.json',
            W / 'old1159-actual-moduledata-names.json', W / 'native316-direct-callee-preflight.json',
            W / 'InspectActualPrerequisiteNames.lean', W / 'metadata-attempt01.log',
            W / 'old-modules-e942.txt', W / 'native316-modules.txt',
            W / 'new316-expected-canonical-names.txt', Path(__file__)]}}
    target = W / 'missing-prerequisite-preflight.json'
    assert not target.exists(), 'One snapshot receipt only'
    target.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'report': str(target), 'report_sha256': digest(target),
        'complete_captures': len(complete), 'captured_modules': len(modules),
        'uncaptured_new_parents': len(uncaptured), 'ordinary_missing_names': len(combined),
        'new_missing_names': report['new_missing_names_after_known_support_deduction']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
