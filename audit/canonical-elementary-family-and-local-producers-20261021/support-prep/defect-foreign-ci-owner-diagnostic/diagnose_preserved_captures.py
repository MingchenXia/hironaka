"""Diagnostic only: read unchanged actual captures, never edit/normalize DAGs."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import shutil
import subprocess

A = Path('/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021')
OUT = Path(__file__).resolve().parent
E = A / 'final-per-module-expressions'
W = Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication')
HELPER = 'Hironaka.MarkedIdeals.MarkedIdeal.IsAdmissibleCentre.eq_1'
NATIVE_HELPER = 'TranscendentalNakamaye.Pending.MarkedIdeals.MarkedIdeal.IsAdmissibleCentre.eq_1'
NATIVE_OWNER = 'TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform'
TARGET = 'Hironaka.Support.CoefficientIdealTowerOperationsOriginalExact'
sha = lambda b: hashlib.sha256(b).hexdigest()
used = {}

def capture(module, side):
    p = E / module / 'attempt1' / (side + '-unfiltered.jsonl.gz')
    compressed = p.read_bytes(); raw = gzip.decompress(compressed)
    used[str(p)] = sha(compressed)
    lines = raw.decode().splitlines(keepends=True)
    records = {x['name']: x for line in lines if (x := json.loads(line))}
    assert len(records) == len(lines)
    return records, {'path': str(p), 'gzip_sha256': sha(compressed), 'uncompressed_sha256': sha(raw),
                     'actual_CIs': len(records)}, {json.loads(line)['name']: line for line in lines}

def tokens(t):
    return [] if t[0] == 'anonymous' else tokens(t[1]) + [t[2]]

def classify_frame_names(a, b, old_frame, new_frame):
    """Classifies unchanged raw names; does not construct a renamed Name/DAG."""
    x, y = tokens(a), tokens(b)
    assert len(x) == len(y)
    changes = []; i = 0
    while i < len(x):
        if x[i:i + 3] == old_frame and y[i:i + 3] == new_frame:
            prefix = (i >= 1 and x[i - 1] == '_@') or (i >= 2 and x[i - 2] == '_hygCtx' and type(x[i - 1]) is int) or (i >= 3 and x[i - 3:i] == ['_@', '_internal', 0])
            tail = i + 4 < len(x) and type(x[i + 3]) is int and x[i + 4] == '_hygCtx'
            assert prefix and tail, (x, y, i)
            changes.append({'module_component_position': i, 'unchanged_numeric_context': x[i + 3]})
            i += 3
        else:
            assert x[i] == y[i], (x, y, i)
            i += 1
    assert changes
    assert [x for x in x if type(x) is int] == [y for y in y if type(y) is int]
    return changes

branches = []
for short, old_frame in [('CoefficientIdealTowerOperationsOriginalExact', 'Hironaka.MarkedIdeal.CoefficientIdeal'),
                         ('DropMembersContainingCentresOriginalExact', 'Hironaka.Invariant.DropMembers'),
                         ('MemberInterTowerAlongOriginalExact', 'Hironaka.Invariant.MemberInterTowerAlong')]:
    module = 'Hironaka.Support.' + short
    old, ofp, _ = capture(module, 'original'); new, nfp, _ = capture(module, 'public')
    changes = []; exact = []
    for name in sorted(old.keys() & new.keys()):
        x, y = old[name], new[name]
        for f in ['exact_name_tree', 'kind', 'levelParams', 'typeRoot', 'valueRoot']:
            assert x[f] == y[f], (name, f)
        assert len(x['fullExprNodes']) == len(y['fullExprNodes'])
        for i, (a, b) in enumerate(zip(x['fullExprNodes'], y['fullExprNodes'])):
            assert a['tag'] == b['tag'] and a['children'] == b['children'], (name, i)
            if a['data'] != b['data']:
                assert a['tag'] in ['lambda', 'forall'] and a['data'][1] == b['data'][1]
                frame_changes = classify_frame_names(a['data'][0], b['data'][0], old_frame.split('.'), module.split('.'))
                changes.append({'actual_CI': name, 'original_node': i, 'public_node': i,
                                'original_exact_node': a, 'public_exact_node': b,
                                'guarded_module_frame_occurrences': frame_changes,
                                'all_numeric_components_and_binderInfo_exact': True})
        exact.append(name)
    branches.append({'module': module, 'original_capture': ofp, 'public_capture': nfp,
                     'all_matched_actual_CIs': exact, 'matched_actual_CIs': len(exact),
                     'all_tags_child_graphs_root_indices_kinds_levels_names_exact': True,
                     'all_observed_non_frame_differences': [],
                     'differing_binder_fields': len(changes),
                     'guarded_frame_occurrences': sum(len(x['guarded_module_frame_occurrences']) for x in changes),
                     'complete_raw_frame_difference_evidence': changes,
                     'original_unmatched_names_retained_in_original_capture': sorted(old.keys() - new.keys()),
                     'new_actual_names_absent_from_this_original_parent': sorted(new.keys() - old.keys())})

owner_export = 'Hironaka.Support.MarkedIdealOperationsMonotoneControlledOriginalExact'
original_owner, original_fp, owner_lines = capture(owner_export, 'original')
public_target, public_fp, public_lines = capture(TARGET, 'public')
o, n = original_owner[HELPER], public_target[HELPER]
fields = ['name', 'exact_name_tree', 'kind', 'levelParams', 'typeRoot', 'valueRoot', 'fullExprNodes']
assert all(o[f] == n[f] for f in fields)
assert o['kind'] == 'theorem' and o['valueRoot'] is not None and len(o['fullExprNodes']) == 137
owner_source = Path(original_fp['path'])
owner_copy = OUT / 'complete-original-MarkedIdealOperationsTransform-owner-unfiltered.jsonl.gz'
shutil.copyfile(owner_source, owner_copy)
assert owner_copy.read_bytes() == owner_source.read_bytes()

metadata_path = W / 'native8-recursive-callee-closure/all-private-generated-diagnostics-classified.json'
metadata = [x for x in json.loads(metadata_path.read_text()) if x.get('relocated_ordinary_callee') == HELPER]
assert metadata and all(x['native_callee'] == NATIVE_HELPER and x['actual_callee_lookup_owner'] == NATIVE_OWNER for x in metadata)
used[str(metadata_path)] = sha(metadata_path.read_bytes())
axiom_path = A / 'all-actual-moduledata-axioms-base323.log'
axiom_text = axiom_path.read_text()
axiom_match = re.search(r'^ACTUAL_ROOT (\S+) ' + re.escape(HELPER) + r' AXIOMS \[([^]]*)\]', axiom_text, re.M)
assert axiom_match
baseline_axioms = [x.strip() for x in axiom_match.group(2).split(',')]
assert set(baseline_axioms) == {'propext', 'Classical.choice', 'Quot.sound'}
owner_source_path = 'TranscendentalNakamaye/TranscendentalNakamaye/Pending/MarkedIdealOperationsTransform.lean'
owner_raw = subprocess.check_output(['git', '-C', '/workspace/archon-publish', 'show', '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07:' + owner_source_path])
assert owner_raw == subprocess.check_output(['git', '-C', '/workspace/archon-publish', 'show', '47cef49895832e3bfe492f66e1f2ac68785187dd:' + owner_source_path])
owner_blob = subprocess.check_output(['git', '-C', '/workspace/archon-publish', 'rev-parse', '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07:' + owner_source_path]).decode().strip()

own_frame_rows = [
    ('TranscendentalNakamaye.Pending.CoefficientIdeal', TARGET),
    ('TranscendentalNakamaye.Pending.DropMembers', 'Hironaka.Support.DropMembersContainingCentresOriginalExact'),
    ('TranscendentalNakamaye.Pending.MemberInterTowerAlong', 'Hironaka.Support.MemberInterTowerAlongOriginalExact')]
(OUT / 'proposed-own-source-frame-input-pairs.tsv').write_text(''.join(a + '\t' + b + '\n' for a, b in own_frame_rows))
(OUT / 'proposed-original-primary-plus-whole-owner-companion.tsv').write_text(
    'TranscendentalNakamaye.Pending.CoefficientIdeal\t' + TARGET + '\n' + NATIVE_OWNER + '\t' + TARGET + '\n')
(OUT / 'proposed-public-target.tsv').write_text(TARGET + '\t' + TARGET + '\n')

report = {'status': 'READ_ONLY_FOREIGN_ACTUAL_CI_OWNER_RESOLVED_AND_ALL_BRANCH_FRAME_DIAGNOSIS',
    'scope': 'Static diagnostic over preserved complete actual captures; not a replacement equality gate.',
    'foreign_actual_public_CI': HELPER, 'actual_native_CI': NATIVE_HELPER,
    'actual_native_physical_owner': NATIVE_OWNER, 'actual_owner_metadata': {'path': str(metadata_path), 'sha256': sha(metadata_path.read_bytes()), 'exact_rows': metadata},
    'whole_original_owner_source': {'path': owner_source_path, 'git_blob_4c6': owner_blob, 'sha256': sha(owner_raw), 'fixed_4c6_and_47cef_bytes_identical': True},
    'whole_original_physical_owner_capture': original_fp,
    'complete_50_CI_owner_copy': {'path': str(owner_copy), 'gzip_sha256': sha(owner_copy.read_bytes()), 'all_50_original_CIs_retained_byte_for_byte': True},
    'whole_new_actual_public_capture': public_fp,
    'whole_foreign_helper_comparison': {'original_record_sha256': sha(owner_lines[HELPER].encode()), 'public_record_sha256': sha(public_lines[HELPER].encode()),
        'fields_compared_without_changes': fields, 'all_fields_exact': True, 'complete_Expr_nodes': 137,
        'typeRoot': o['typeRoot'], 'valueRoot': o['valueRoot'], 'whole_body_present': True,
        'only_record_module_bucket_differs': o['module'] != n['module'],
        'filtered_single_CI_file_written': False},
    'existing_public_baseline_axiom_evidence': {'path': str(axiom_path), 'sha256': sha(axiom_path.read_bytes()),
        'line': axiom_text[:axiom_match.start()].count('\n') + 1, 'actual_physical_owner': axiom_match.group(1),
        'actual_axioms': baseline_axioms, 'fresh_native_or_new_support_axiom_replay_claimed': False},
    'all_branch_diagnoses': branches,
    'bounded_companion_input_plan': {
        'input': 'proposed-original-primary-plus-whole-owner-companion.tsv',
        'meaning': 'Unchanged V3 original-modules output-bucket pairs, retaining both COMPLETE actual original physical parents. Never edit the module field or any CI/DAG payload in an existing capture.',
        'source_frame_input': 'proposed-own-source-frame-input-pairs.tsv',
        'private_owner_caution': 'The companion output bucket does NOT authorize a broad private/callee owner rewrite MarkedIdealOperationsTransform→CoefficientIdeal support. Retain actual public callee-owner mappings; this helper itself is already node-for-node exact.',
        'permitted_narrow_runtime_for_frontier_only': 'Reuse immutable complete owner evidence if the existing transport accepts its original module bucket; otherwise unchanged-V3 re-export ONLY the full genuine companion parent under the target bucket. Preserve the original primary capture and every new actual public CI.',
        'no_CI_filter_or_waiver': True, 'no_frozen_V3_profile_change': True,
        'raw_FAIL_reports_preserved': True},
    'original_or_public_CI_DAG_numeric_binder_or_proof_payload_edits': 0,
    'production_source_or_Git_edits': False, 'Lean_build_kernel_Expr_or_axiom_runtime_invoked': False}
(OUT / 'owner-and-all-branches-diagnostic.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
for path, digest in used.items(): assert sha(Path(path).read_bytes()) == digest
print(json.dumps({'status': report['status'], 'native_owner': NATIVE_OWNER, 'helper_full137nodes_exact': True,
    'complete_original_owner_CIs_retained': len(original_owner),
    'branches': [{'module': b['module'], 'matched': b['matched_actual_CIs'], 'binder_fields': b['differing_binder_fields'], 'frame_occurrences': b['guarded_frame_occurrences'], 'non_frame_differences': 0} for b in branches]}, indent=2))
