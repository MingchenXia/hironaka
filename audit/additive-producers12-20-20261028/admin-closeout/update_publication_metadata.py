#!/usr/bin/env python3
"""Compose final49 administrative metadata from closed immutable receipts."""
from pathlib import Path
import copy
import hashlib
import json

C = Path(__file__).resolve().parent
E = C.parent
D = E.parents[1]
A = D / 'audit/disjoint-producers-20261028'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
first33 = E / 'first33-publication/audit/disjoint-producers-20261028/publication-verification.json'
old = json.loads(first33.read_text())
assert old['status'] == 'PASS_SOURCE_FAITHFUL_COMPOSITE33_PUBLICATION'
assert (A / 'publication-verification.json').read_bytes() == first33.read_bytes()
peer_path = E / 'independent/final-review.json'
assert sha(peer_path) == '2ad6f39778966d1f351cd87faa30f0ec5d24c644d463285f5a580712e43f429b'
peer = json.loads(peer_path.read_text())
assert peer['before_after_all_unchanged'] and not peer['remaining_findings']
assert peer['new_all_gate_exits_zero'] and peer['new_gate_warnings'] == 0
freeze = json.loads((E / 'final-new16-freeze.json').read_text())
install = json.loads((E / 'installation-plan.json').read_text())
marker = json.loads((E / 'root-marker-acceptance.json').read_text())
assert marker['independent_review_sha256'] == sha(peer_path)
assert sha(D / marker['path']) == marker['ready_sha256']
assert sha(D / marker['premarker_capture']) == marker['premarker_sha256']
assert (D / marker['path']).read_text().replace('\\leanok\n', '') == (D / marker['premarker_capture']).read_text()

source_rows = old['source_modules'] + freeze['sources']
assert len(source_rows) == len({row['module'] for row in source_rows}) == 49
for row in source_rows:
    assert sha(D / row['source_path']) == row['source_sha256']
    for path, digest in row['all_compiled_parts'].items():
        assert sha(D / path) == digest, path
old_plan = json.loads((A / 'plan.json').read_text())
for path, digest in old_plan['old_file_guards'].items():
    assert sha(D / path) == digest, path

v = copy.deepcopy(old)
v.update({
    'status': 'PASS_SOURCE_FAITHFUL_COMPOSITE49_PUBLICATION',
    'native_revision': install['native_revision'],
    'native_revision_semantics': 'Latest additive source; each cohort retains its own fixed source snapshot below.',
    'native_revisions': {'first33': old['native_revision'], 'additive16': install['native_revision']},
    'previous_standalone_checkpoint': install['standalone_base'],
    'whole_original_modules': 43, 'complete_original_support_files': 6,
    'complete_original_support_declarations': 9, 'physical_modules': 49,
    'whole_original_blueprint_chapters': 38,
    'whole_original_blueprint_proofs': 120, 'additional_support_written_proofs': 12,
    'complete_written_proofs': 132, 'literal_bindings': 270,
    'actual_physical_declarations': 978, 'unique_new_target_kernels': 49,
    'unique_new_allphysical_type_wholevalue_audits': 49,
    'strict_full_expression_types_values_and_proofs': 'PASS_ALL49_COMPOSED_BY_EXACT_IDENTITY',
    'numeric_or_proof_name_rewrites': False, 'old_kernel_or_Expr_gate_replays': 0,
    'copied_original_blueprint_pages_unchanged': 38, 'ready_nodes': 143,
    'unattached_ordinal_helper_nodes_not_ready': 2,
    'old_guard_files_byte_preserved': 3678, 'README_changed': False,
    'prior33_publication': {'path': str(first33.relative_to(D)), 'sha256': sha(first33),
                            'standalone_checkpoint': install['standalone_base']},
    'prior33_independent_review': old['independent_review'],
    'independent_review': {'path': str(peer_path.relative_to(D)), 'sha256': sha(peer_path)},
    'prior33_root_frontend': old['current_root_frontend'],
    'current_root_frontend': {'path': str((E / 'narrow-current-root-frontend.json').relative_to(D)),
                              'sha256': sha(E / 'narrow-current-root-frontend.json'), 'exit': 0},
    'current_root_artifacts': json.loads((E / 'narrow-current-root-frontend.json').read_text())['all_current_root_artifacts'],
    'source_modules': source_rows,
    'source_cohorts': [
        {'id': 'first33', 'native_revision': old['native_revision'],
         'modules': [row['module'] for row in old['source_modules']],
         'whole_modules': 29, 'support_files': 4, 'support_declarations': 7,
         'physical_declarations': 748, 'whole_BP_chapters': 26,
         'written_proofs': 100, 'literal_bindings': 209, 'ready_nodes': 108,
         'unique_kernel_checks': 33, 'unique_physical_audits': 33,
         'reused_only_after_exact_source_BP_math_artifact_identity': True},
        {'id': 'additive16', 'native_revision': install['native_revision'],
         'modules': [row['module'] for row in freeze['sources']],
         'whole_modules': 14, 'support_files': 2, 'support_declarations': 2,
         'physical_declarations': 230, 'whole_BP_chapters': 12,
         'written_proofs': 32, 'literal_bindings': 61, 'ready_nodes': 35,
         'unique_kernel_checks': 16, 'unique_physical_audits': 16,
         'before_after_pins_unchanged': 4601},
    ],
    'support_blueprint_marker_changes': old['support_blueprint_marker_changes'] + [{
        'path': marker['path'], 'nodes': marker['ready_nodes_added'],
        'premarker_capture': marker['premarker_capture'],
        'premarker_sha256': marker['premarker_sha256'], 'ready_sha256': marker['ready_sha256'],
    }],
    'publication_paths': sorted(set(old['publication_paths']) | {
        row['destination_path'] for row in install['source_modules'] + install['support_extracts'] + install['whole_blueprints'] + install['documentation_pointers']
    }),
    'whole_blueprint_pins': [
        {'path': row['destination_path'], 'sha256': row['destination_sha256'], 'native_revision': old['native_revision']}
        for row in old_plan['blueprints']
    ] + [
        {'path': row['destination_path'], 'sha256': row['destination_sha256'], 'native_revision': install['native_revision']}
        for row in install['whole_blueprints']
    ],
    'final_compiled_umbrella_binding_probe': {
        'path': str((E / 'independent/literal-bindings-exit.json').relative_to(D)),
        'sha256': sha(E / 'independent/literal-bindings-exit.json'), 'exit': 0, 'bindings': 270},
    'latest_root_marker_acceptance': {'path': str((E / 'root-marker-acceptance.json').relative_to(D)),
                                     'sha256': sha(E / 'root-marker-acceptance.json')},
    'standalone_original_closed': ['G2', 'G5', 'G6', 'G7'],
    'standalone_original_open': ['G1', 'G3', 'G4', 'G8', 'G9'],
    'native_G9_backlog_exported': False, 'source_goal_closure_claimed': False,
    'merge_authorized': False,
    'latest_user_constraint': 'Do not merge the Hironaka repository; finish existing lanes, publish their changes and stop.',
    'existing_lanes_only': True,
    'build_scope': 'Exact new-module batches, unique new-target kernels/physical audits and one changed-source umbrella frontend per additive cohort. No clean full-project build claimed.',
    'historical_failures': 'All original failures and superseded states are retained. First33 verification, manifest, readmes, verifier and scope/API snapshots are archived before current49 administrative updates.',
})
assert len(v['whole_blueprint_pins']) == 38
assert sum(row['nodes'] for row in v['support_blueprint_marker_changes']) == 12
assert len(v['publication_paths']) == 97
(A / 'publication-verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('COMPOSED49: 43 whole + 6 support files; 978 physical declarations, 270 bindings, 132 proofs, 143 ready nodes')
