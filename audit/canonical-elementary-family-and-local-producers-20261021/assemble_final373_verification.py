#!/usr/bin/env python3
"""Assemble completed immutable gates; no Lean, source replay, or capture invocation."""
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json

A = Path(__file__).resolve().parent
R = A.parent.parent

def read(name):
    return json.loads((A / name).read_text())

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def evidence(name):
    path = A / name
    assert path.is_file(), name
    return {"path": str(path.relative_to(R)), "sha256": digest(path), "bytes": path.stat().st_size}

def exit_zero(name):
    assert (A / name).read_text().strip() == "0", name

expr = read('final-per-module-expressions/status.json')
kernel = read('new-kernel-status.json')
physical = read('final-physical-ci-axioms.json')
source = read('source-replay-receipt.json')
classification = read('all-notation-classification-final-attempt01/verification.json')
math = read('all-notation-classification-final-attempt01/strict-all-mathematical-roots-comparison.json')
isolation = read('all-notation-isolation-final-attempt01/verification.json')
logical = read('all-notation-isolation-final-attempt01/all-notation-logical-isolation.json')
independent = read('independent-source-replay-review/final-extended-cohort/final-installed-static-review.json')
bindings = read('final373-literal-binding-inventory/inventory.json')
partition = read('deferred-complete-module-partition.json')
index = read('blueprint-external-index-final373-support-nodes-static.json')
pdf = read('blueprint-pdf-final-attempt04/verification.json')
pdf_labels = read('blueprint-pdf-final-attempt04/typesetting-warning-review-corrected-exact-tokens.json')
provenance = read('provenance.json')
blueprints = read('blueprint-provenance.json')
module_names = set(expr['modules'])
assert len(module_names) == len(provenance) == 373
assert module_names == set(kernel['modules']) == {x['destination_module'] for x in provenance}
assert expr['captured_and_compared_modules'] == expr['total_new_modules'] == 373
assert expr['status'].startswith('BLOCKED_'), 'Raw status must remain truthful and unchanged.'
assert expr['public_roots_filtered'] == expr['proof_type_token_edits'] == 0
assert not expr['defeq_or_alpha_comparison'] and not expr['raw_frontend_differences_waived']
raw_statuses = Counter(x['every_actual_new_root_comparison']['status'] for x in expr['modules'].values())
assert raw_statuses == {'EXACT_ALL_FULL_EXPR_DAG_MATCH': 363, 'BLOCKED_EXACT_DIFFERENCE': 10}
blocked = sorted(n for n, x in expr['modules'].items() if x['every_actual_new_root_comparison']['status'] == 'BLOCKED_EXACT_DIFFERENCE')
assert set(blocked) == set(math['module_counts'])
assert classification['status'] == 'PASS_ALL_MATHEMATICAL_ROOTS_STRICT_WITH_SIXTY_DISCLOSED_FRONTEND_DEFINITIONS'
assert classification['mathematical_comparison_exit'] == 0
assert not classification['parser_body_structural_equality_claimed']
assert not classification['raw_Expr_Name_number_binder_or_proof_normalization']
assert math['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH'
assert math['old']['all_actual_constants'] == math['native']['all_actual_constants'] == 178
assert math['missing'] == math['native_extras'] == math['differences'] == []
assert math['fallbacks'] == math['auxiliaries_skipped'] == math['proof_numbers_erased'] == math['binder_names_erased'] == 0
assert isolation['status'] == 'PASS' and isolation['exit'] == 0
assert isolation['source_inputs_unchanged'] and isolation['native_and_control_inputs_unchanged']
assert isolation['expected_typed_public_frontend_definitions'] == 60
assert logical['direct_references_to_public_parser_roots'] == []
assert logical['all_public_moduleData_constants'] == 24090
assert logical['all_public_moduleData_modules'] == 1533
assert logical['other_actual_constants_scanned'] == 24030
assert logical['actual_new_moduleData_modules'] == 373
assert len(logical['actual_original_and_public_parser_roots']) == 120
assert len(logical['actual_upstream_only_public_names_verified_absent']) == 17
assert kernel['status'] == 'PASS_ALL373_NEW_EXACT_KERNEL_REPLAYS'
assert kernel['passed'] == kernel['total'] == 373
assert all(x['exit_code'] == 0 for x in kernel['modules'].values())
assert physical['status'] == 'PASS_ALL_ACTUAL_PHYSICAL_CI_PAYLOAD_AXIOMS'
assert physical['actual_modules'] == 1533 and physical['actual_physical_root_observations'] == 24090
assert not physical['roots_frontend_or_helpers_filtered']
assert not physical['physical_root_payload_replaced_by_environment_Name_lookup']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(x['physical_payload_transitive_axioms']) <= allowed for x in physical['all_physical_root_rows'])
actual_new_rows = [x for x in physical['all_physical_root_rows'] if x['actual_moduleData_owner'] in module_names]
assert len(actual_new_rows) == expr['all_actual_public_roots'] == 5709
assert expr['all_original_parent_roots_retained'] == 6371
# Every actual new physical module-owned Name observation is present in its unfiltered capture.
for name, m in expr['modules'].items():
    assert m['capture_exit'] == 0 and m['scoped_comparison_complete']
    assert m['public_roots_filtered'] == 0 and not m['original_parent_rows_modified']
    observed = Counter(x['actual_name'] for x in actual_new_rows if x['actual_moduleData_owner'] == name)
    assert observed == Counter(m['captures']['public-unfiltered']['actual_root_names']), name
    report = m['every_actual_new_root_comparison']
    assert digest(R / report['report']) == report['report_sha256'], name
assert sum(x['captures']['public-unfiltered']['actual_roots'] for x in expr['modules'].values()) == 5709
assert source['status'] == 'PASS_EXACT_SOURCE_AND_BLUEPRINT_REPLAY'
assert source['new_source_files'] == 373 and source['new_written_proofs'] == 1125
assert source['new_complete_blueprint_chapters'] + source['new_complete_original_node_extract_chapters'] == len(blueprints) == 349
assert source['external_prerequisite_label_anchors'] == 123
assert source['base_parent_complements'] == 7 and source['supplementary_missing_original_prerequisite_extracts'] == 19
assert source['complete_new_whole_modules'] == 345 and source['pure_existing_support_import_adapters'] == 2
assert 345 + 7 + 19 + 2 == 373
assert source['old1159_math_files_preserved'] == 1159 and source['original_proof_token_edits'] == 0
assert source['deferred_complete_modules'] == source['deferred_complete_blueprint_chapters'] == 2
assert bindings['new_unique_local_bindings'] == 2298 and bindings['whole_unique_local_bindings'] == 8424
assert bindings['upstream_attachments_excluded_from_local_claim']
assert independent['status'] == 'PASS_FINAL_EXTENDED_INSTALLED_STATIC_SOURCE_BP_PRESERVATION_AND_NO_OP'
assert independent['before_after_public_input_fingerprint_equal']
assert independent['Lean_kernel_Expr_native_runtime_invocations'] == independent['production_mutations'] == independent['logical_type_or_proof_payload_edits'] == 0
assert independent['no_op_intercepted_equal_receipt'][0]['sha256'] == digest(A / 'source-replay-receipt.json')
assert index['minimum_external_anchors'] == 123 and index['master_actual_inputs'] == 969
assert index['all_new_uses_ref_eqref_resolved'] and index['duplicate_labels'] == {}
assert pdf['status'] == 'PASS_RENDERED_GENERATED_TYPESETTING_COPY'
assert all(x['exit'] == 0 for x in pdf['passes']) and len(pdf['passes']) == 3
assert pdf['published_inputs_unchanged'] and pdf['published_source_edits'] == 0
assert pdf_labels['render_pages'] == 1379
assert pdf_labels['all103_render_undefined_labels_occur_only_in_preserved_old619_sources']
assert pdf_labels['new349_undefined_actual_literal_reference_tokens'] == []
for fn in ['build-final373-attempt01.exit', 'kernels-final373-attempt01.exit', 'all-physical-ci-axioms-final373.exit', 'lake-test-final373.exit', 'literal-blueprint-bindings-final373.exit']:
    exit_zero(fn)
assert 'Build completed successfully (5681 jobs).' in (A / 'build-final373-attempt01.log').read_text()
assert '13840 declarations, all within [propext, Classical.choice, Quot.sound]' in (A / 'lake-test-final373.log').read_text()
assert 'NEW_SOURCE_CHAPTERS 2298 MISSING 0' in (A / 'literal-blueprint-bindings-final373.log').read_text()
assert 'WHOLE_DOCUMENT 8424 MISSING 0' in (A / 'literal-blueprint-bindings-final373.log').read_text()
profiles = read('initial-port-plan.json')['toolchain_profiles']
assert len(profiles) == 4
assert all(digest(R / p) == h for p, h in profiles.items())

files = [
    'provenance.json', 'blueprint-provenance.json', 'source-replay-receipt.json', 'source-replay-final373.log',
    'sync_frozen_sources.py', 'additive_frozen_cohort.py', 'initial-port-plan.json', 'all-standalone-modules.txt',
    'base323-frozen-before-additive40/immutable-base-source-and-kernel-parts.json',
    'deferred-complete-module-partition.json',
    'support-prep/canonical-offzero-feasibility/constraint-and-publication-review-canonical.json',
    'build-final373-attempt01.log', 'build-final373-attempt01.exit',
    'new-kernel-status.json', 'kernels-final373-attempt01.log', 'kernels-final373-attempt01.exit',
    'final-per-module-expressions/status.json', 'expressions-final373-owner-profile-attempt02.log', 'expressions-final373-owner-profile-attempt02.exit',
    'all-notation-classification-final-attempt01/verification.json',
    'all-notation-classification-final-attempt01/strict-all-mathematical-roots-comparison.json',
    'all-notation-classification-final-attempt01/raw-all-ten-parents-comparison.json',
    'all-notation-isolation-final-attempt01/verification.json',
    'all-notation-isolation-final-attempt01/all-notation-logical-isolation.json',
    'support-prep/principal-parts/three-notation-source-generation-after04-final.json',
    'additive40-frozen-preparation/seven-notation-source-generation-production-after-doc-placement.json',
    'AllActualStandaloneRootsPhysicalCI.lean', 'final-physical-ci-axioms.json', 'all-physical-ci-axioms-final373.log', 'all-physical-ci-axioms-final373.exit',
    'lake-test-final373.log', 'lake-test-final373.exit', 'final373-literal-binding-inventory/inventory.json',
    'literal-blueprint-bindings-final373.log', 'literal-blueprint-bindings-final373.exit', 'CheckLiteralBlueprintBindings.lean',
    'new-original-companion-owner-modules.json', 'new-original-verbatim-root-witnesses.json', 'new-actual-callee-owner-profiles.json',
    'additive40-original-prerequisite-extracts/plan.json', 'additive40-original-elaboration-contexts.json', 'additive40-original-support-imports.json',
    'blueprint_original_node_extracts.py', 'blueprint-original-node-extract-plan.json', 'blueprint-documentation-overlay-plan.json',
    'blueprint-external-index-final373-support-nodes-static.json', 'blueprint-final373-exact-six-token-review.json',
    'blueprint-pdf-final-attempt04/verification.json', 'blueprint-pdf-final-attempt04/typesetting-warning-review-corrected-exact-tokens.json',
    'independent-source-replay-review/final-extended-cohort/final-installed-static-review.json',
    'independent-source-replay-review/final-extended-cohort/old-blueprint-count-clarification.json',
]
manifest = {
    'status': 'PASS_FINAL373_MATHEMATICAL_SYNC_WITH_DISCLOSED_FRONTEND_CLASSIFICATION_AND_TWO_WHOLE_MODULE_DEFERRALS',
    'assembled_at_utc': datetime.now(timezone.utc).isoformat(),
    'method': 'Aggregate already completed immutable gate evidence. This assembly invokes no Lean, kernel, exporter, comparator, source synchronizer, renderer, Git, or publication action.',
    'source_revisions': {'base_ordinary_Git': source['actual_source_revision'], 'additive40_ordinary_Git': source['additive_ordinary_source_revision'], 'base_accepted_checkpoint': source['accepted_checkpoint'], 'source_main_merge_claimed': False},
    'scope': {
        'new_physical_Lean_modules': 373, 'whole_original_modules': 345, 'complete_missing_original_parent_complements': 7,
        'pure_existing_support_import_adapters': 2, 'complete_original_prerequisite_extract_files': 19,
        'unchanged_base_new_modules_reused': 323, 'additive_whole_modules': 40, 'additive_support_files': 10,
        'all_physical_source_modules_including_root': 1533, 'all_retained_new_modules_reachable': True,
        'new_source_facing_BP_chapters': 349, 'whole_original_BP_chapters': 346, 'complete_original_node_extract_BP_chapters': 3,
        'complete_written_proof_environments': 1125, 'documentation_only_external_index_chapters': 1, 'minimum_external_label_anchors': 123,
        'master_chapter_inputs': 969, 'master_reachable_TeX_files_including_master': 970, 'explicit_native_only_upstream_bindings': 17,
    },
    'gates': {
        'fresh_full_standalone_build': {'status': 'PASS', 'command': 'lake --no-cache build --wfail Hironaka', 'jobs': 5681, 'warnings': 0},
        'exact_most_private_new_kernel_replay': {'status': 'PASS', 'new_modules': 373, 'actual_new_CI_observations_covered': 5709, 'old1159_independent_kernel_replay_repeated': False},
        'full_mathematical_expressions': {
            'status': 'PASS_ALL5649_NEW_MATHEMATICAL_ROOTS_STRICT', 'actual_new_physical_CI_observations': 5709,
            'whole_original_parent_root_observations_retained': 6371, 'mathematical_roots_strict': 5649,
            'raw_exact_module_comparisons': 363, 'raw_blocked_notation_module_comparisons': 10,
            'raw_global_status_preserved': expr['status'], 'raw_capture_or_report_status_overwritten': False,
            'raw_BLOCKED_notation_modules': blocked, 'raw_owner_and_foreign_helper_failures_preserved': True,
            'notation_parent_mathematical_roots_strict': 178, 'disclosed_new_frontend_definitions': 60,
            'frontend_body_structural_equality_claimed': False,
            'separate_frontend_gates': ['literal original notation source generation', 'actual native and public compiler output types', 'zero logical constant references from all other actual physical CIs', 'all-root own-payload standard axiom scan', 'exact installed kernel replay'],
            'whole_environment_nonfrontend_CIs_scanned_for_frontend_references': 24030, 'direct_logical_references_to_frontends': 0,
            'public_root_filtering': 0, 'proof_or_type_token_edits': 0, 'Expr_Name_number_binder_or_proof_normalization': False,
            'defeq_or_alpha_comparison': False, 'frozen_exporter_or_comparator_changed': False,
            'actual_owner_scope_inputs': 'Recorded actual physical owner and numeric-scope-preserving module-frame inputs to the unchanged frozen exporter; complete original captures retained. Genuine foreign-owner companion scope and two already-exact foreign original rows are explicit input witnesses, never edited DAG records.',
        },
        'all_physical_CI_own_payload_axioms': {'status': 'PASS', 'physical_CI_observations': 24090, 'physical_modules': 1533, 'allowed_axioms': sorted(allowed), 'root_payload_replaced_by_global_Name_lookup': False, 'frontend_private_generated_and_duplicate_owner_roots_retained': True, 'distinct_global_names_with_multiple_physical_owners': len(physical['duplicate_global_names_with_distinct_physical_owners']), 'command_options': ['-DmaxHeartbeats=0', '-DmaxRecDepth=10000'], 'historical_Name_based_audit_unmodified': True},
        'documented_lake_test': {'status': 'PASS', 'curated_declarations': 13840, 'supplemental_to_all_physical_CI_gate': True},
        'literal_local_BP_bindings': {'status': 'PASS', 'new_unique_local_names': 2298, 'whole_document_unique_local_names': 8424, 'missing_local_names': 0, 'upstream_only_names_explicitly_separate': 17},
        'dual_fixed_source_no_op': {'status': 'PASS', 'independent_guarded_no_op_equal_receipt': True, 'production_inputs_unchanged': True, 'source_or_proof_payload_edits': 0},
        'independent_source_BP_preservation_review': {'status': 'PASS', 'runtime_replays_by_reviewer': 0, 'complete_selected_original_nodes': 32, 'additive_support_complete_original_declarations': 40},
        'new_BP_exact_reference_resolution': {'status': 'PASS', 'new_chapters': 349, 'unresolved_NEW_literal_labels': 0, 'duplicate_labels': 0, 'external_anchors_are_local_theorem_claims': False},
        'generated_copy_PDF': {'status': 'PASS_WITH_DISCLOSED_PRESERVED_LEGACY_WARNINGS', 'passes': 3, 'pages': 1379, 'published_source_edits': 0, 'generated_only_neutral_typesetting_overlay': True, 'legacy_undefined_labels_old619_only': 103, 'NEW349_undefined_reference_labels': 0, 'original_as_is_LaTeX_compilation_claimed': False},
    },
    'preservation': {'old_Lean_files_byte_unchanged': 1159, 'old_BP_files_byte_unchanged': 619, 'old_BP_master_separately_append_only': True, 'historical_guard_numeric620_means_619_files_plus_master': True, 'frozen_profiles_unchanged': profiles, 'base323_source_and_owned_kernel_parts_unchanged': True, 'all_failed_attempts_raw_differences_and_old_receipts_retained': True},
    'deferred_whole_modules': partition['deferred_complete_modules'],
    'deferred_whole_BP_chapters': partition['deferred_complete_blueprint_chapters'],
    'limits': [
        'Two entire source modules and two entire chapters remain deferred; their complete originals and raw failures remain in immutable audit captures. No declaration filtering within exported modules.',
        'The ten notation-parent raw comparisons remain BLOCKED; all mathematical roots pass strict full-expression comparison and the sixty frontend definitions pass separate source/type/isolation/kernel/axiom gates. Frontend body identity is not claimed.',
        'Seventeen declaration attachments are explicitly upstream-only and are not counted as locally exported or locally verified bindings.',
        'This source synchronization does not close all original G1-G9 goals. G1, G3, G4, G8, and G9 remain open; G2, G5, G6, and G7 were accepted in their recorded scopes.',
        'Centre-relative geoStrictTransform identities are not promoted to ordinary exceptional-locus strictTransform identities without the missing dictionary.',
        'Git commits, pushes, PR updates, and source-main merge status are outside this verification assembly and are owned by the root agent.',
    ],
    'evidence': {name: evidence(name) for name in files},
    'assembler': {'path': str(Path(__file__).relative_to(R)), 'sha256': digest(Path(__file__))},
}
(A / 'final373-verification.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
report = '''The final standalone export passes all mathematical synchronization gates for **373 new Lean files**, with **349 source-facing blueprint chapters and 1,125 complete written proofs**. It preserves the existing 1,159 Lean files, 619 blueprint files, and four frozen profiles; the old master receives only the recorded appended imports. The fixed ordinary source revisions are `4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07` and `47cef49895832e3bfe492f66e1f2ac68785187dd`.

- Full build: 5,681 jobs, zero warnings. Exact installed-kernel replay: all 373 new modules.
- Full mathematical expressions: **5,649 actual new roots match strictly**. All 5,709 actual new CI observations and 6,371 complete original-parent observations remain covered.
- The ten notation-parent raw reports remain **BLOCKED**. Their 178 mathematical roots match strictly; 60 disclosed compiler frontend definitions separately pass literal source generation, actual native/public type checks, zero logical-dependency checks, kernel replay, and axiom checks. Frontend body identity is not claimed.
- Own-payload axiom audit: all **24,090 physical CI observations across 1,533 modules** use only `propext`, `Classical.choice`, and `Quot.sound`. Every private, generated, frontend, and duplicate-owner observation is retained. `lake test` also passes its 13,840 curated declarations.
- Literal local bindings: 2,298 new / 8,424 whole-document unique names, zero missing. Seventeen explicitly upstream-only attachments remain separate. All new chapter references resolve through the disclosed 123-anchor external index.
- Fixed-source replay and independent guarded no-op/preservation review pass. The generated typesetting copy renders in three passes to 1,379 pages; 103 preserved legacy undefined-reference warnings belong only to old chapters.

Two entire modules and their chapters remain deferred: `HironakaOriginalGlobalOffZero` and `HironakaOriginalGlobalProperModification`. Their complete source drafts and failed strict comparisons are preserved. The immutable imported local-inverse type prevents their exact synchronization under the existing preservation rules.

G1, G3, G4, G8, and G9 remain open. This export does not claim full Hironaka completion, arbitrary analytic embedding descent, or an unproved identification of centre-relative and ordinary strict transforms. G2, G5, G6, and G7 retain their previously accepted scopes.

The machine-readable manifest [final373-verification.json](final373-verification.json) binds every final gate by SHA-256, including the truthful raw BLOCKED reports and their separate frontend classification. Git publication and PR updates are handled separately by the root agent.
'''
(A / 'final-report.md').write_text(report)
print(json.dumps({'status': manifest['status'], 'verification': evidence('final373-verification.json'), 'report': evidence('final-report.md')}, indent=2))
