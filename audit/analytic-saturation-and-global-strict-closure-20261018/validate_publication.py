"""Validate the fixed native313 increment's recorded gates and current frozen bytes.

This reads source, captures and installed artifacts. It launches no Lean, export,
kernel replay or network operation; the separate tools reproduce those checks.
"""
from pathlib import Path
import hashlib, json, re, subprocess
from urllib.parse import unquote
from validate_previous_reuse import validate_reuse

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
PREVIOUS = A.parent / 'analytic-coefficient-dictionary-and-chosen-overlaps-20261015'
BASE = '9af2f7c9484b15a45282d098396261a682fb3f93'
REV = 'd39b015d6674af8ceb12e0fa6a5198e93b2afba5'
CP = 'fb8088374e308e1ae1c103a276b6fe996c3a936d'

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def load(name):
    return json.loads((A / name).read_text())

def expect(record, **fields):
    for key, value in fields.items():
        assert record[key] == value, (key, record[key], value)

source = load('published-source-replay.json')
expect(source,
    status='PASS_COMPLETE_NORMAL_PUBLISHED_SOURCE_REPLAY_AND_1002_PREVIOUS_SOURCE_GUARD',
    accepted_native_checkpoint=CP, normal_published_revision=REV,
    previous_public_main=BASE, previous_mathematical_sources_byte_identical=1002,
    whole_original_modules=9, original_pure_support_modules=4,
    complete_original_support_declarations=11, complete_blueprint_chapters=9,
    complete_original_blueprint_proofs=19, local_blueprint_bindings=26,
    new_module_targets=13, root_changes_only_recorded_imports=4,
    private_ledger_required=False, original_type_proof_text_changes=0,
    frozen_tool_profiles_unchanged=True)
for record in load('frozen-tool-profiles.json'):
    assert digest(ROOT / record['path']) == record['sha256'], record['path']

whole = load('whole-module-full-expression-comparison.json')
fragments = load('fragment-full-expression-comparison.json')
proofs = 0
for report, count, module_count in [(whole, 52, 9), (fragments, 11, 4)]:
    expect(report, status='EXACT_ALL_FULL_EXPR_DAG_MATCH', missing=[],
        native_extras=[], approved_native_extras=[], unapproved_native_extras=[],
        differences=[], fallbacks=0, auxiliaries_skipped=0,
        proof_numbers_erased=0, binder_names_erased=0,
        defeq_or_alpha_comparison=False, metadata_preserved_in_full=True)
    assert report['old']['all_actual_constants'] == count
    assert report['native']['all_actual_constants'] == count
    assert len(report['module_counts']) == module_count
    assert sum(r['constants'] for r in report['module_counts'].values()) == count
    for record in report['module_counts'].values():
        assert record['constants'] == record['types_exact'] == record['values_exact']
        assert record['theorems'] == record['theorem_proofs_exact']
        proofs += record['theorems']
    assert report['comparator']['sha256'] == digest(
        ROOT / 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py')
assert proofs == 59
captures = {r['path']: r for r in load('recorded-full-expression-captures.json')}
assert len(captures) == 6
for name, record in captures.items():
    assert digest(A / record['gzip_path']) == record['gzip_sha256'], name
    assert (A / record['gzip_path']).stat().st_size == record['gzip_bytes']
for report in [whole, fragments]:
    for side in ['old', 'native']:
        assert captures[Path(report[side]['path']).name]['sha256'] == report[side]['sha256']
assert 'PASS_ALL_63_RECORDED_ACTUAL_ROOTS_AND_59_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON' in (
    A / 'recorded-full-expression-replay.log').read_text()
selection = load('fragment-original-root-selection.json')
expect(selection, all_original_parent_roots=129, all_actual_public_support_roots=11,
    complete_selected_original_roots=11, public_roots_filtered_or_omitted=0)
assert len(selection['unselected_original_parent_roots_outside_this_eleven_declaration_extraction']) == 118
assert load('whole-module-full-expression-comparison-initial-before-instance-context.json')['status'] == 'BLOCKED_EXACT_DIFFERENCE'

build = (A / 'build-03-original-instance-context.log').read_text()
assert 'Build completed successfully (5007 jobs).' in build
assert not re.search(r'(?im)^.*\b(?:warning|error):', build)
actual = (A / 'all-actual-roots-final.log').read_text()
assert 'ALL_LIBRARY_MODULES 1016; ALL_LIBRARY_ACTUAL_ROOTS 16926; NEW_MODULES 13; NEW_ACTUAL_ROOTS 63; EXACT_BINDINGS 26; MISSING 0; STANDARD_THREE_ONLY' in actual
assert 'SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4275; MISSING 0' in actual
assert 'ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5434; MISSING 0' in actual
for name, count in [('new-local-bindings.json', 26),
                    ('complete-blueprint-local-bindings.json', 4275),
                    ('all-document-local-bindings.json', 5434)]:
    bindings = load(name)
    assert len(bindings) == len(set(bindings)) == count

peer = load('g3-original-support-and-context-review.json')
assert peer['status'] == 'PASS_INDEPENDENT_ENTIRE_ORIGINAL_SOURCE_AND_CONTEXT_TEXT_REVIEW'
expect(peer, normal_published_revision=REV, fixed_native_checkpoint=CP,
    complete_original_support_declarations=11, pure_support_modules=4,
    original_full_support_parents=4, owned_whole_module_source_replays=9,
    recorded_whole_import_substitutions=3,
    recorded_declaration_local_original_instance_restorations=1,
    proof_type_body_token_changes=0,
    all_original_scope_variables_universes_omit_Ambient_Tower_retained=True)
for path, sha in peer['source_hashes'].items():
    assert digest(ROOT/path) == sha
for path, sha in peer['metadata_hashes'].items():
    assert digest(A/path) == sha
assert peer['observed_final_whole_expression_gate']['sha256'] == digest(A/'whole-module-full-expression-comparison.json')

before = load('kernel-artifacts-before.json')
after = load('kernel-artifacts-after.json')
assert before == after
assert after['mathematical_modules_including_root'] == after['kernel_data_parts'] == 1016
assert len(after['sources']) == 1016
current_sources = {'Hironaka.lean'} | {str(p.relative_to(ROOT)) for p in (ROOT / 'Hironaka').rglob('*.lean')}
assert current_sources == set(after['sources'])
for category in ['sources', 'compiled_kernel_data_parts', 'compiled_import_metadata_sha256']:
    for name, sha in after[category].items():
        assert digest(ROOT / name) == sha, (category, name)
reuse = validate_reuse(A, after)
expect(reuse, reused_preceding_modules=1002, fresh_new_modules=13,
    fresh_additional_changed_previous_kernel_modules=0,
    fresh_mathematical_modules=13, all_1002_previous_mathematical_sources_byte_identical=True)
kernel = load('incremental-kernel-replay.json')
expect(kernel,
    status='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY',
    new_modules=13, fresh_mathematical_modules=13, new_module_exact_inventory=True,
    import_root_replayed_with_installed_LeanChecker=True,
    full_sources_and_kernel_parts_unchanged=True, total_local_modules=1016,
    total_kernel_parts=1016, previous_nonroot_modules_reused_from_identical_verified_checkpoint=1002,
    lean_num_threads=1, fresh_full_library_replay_claimed=False)
assert 'REPLAYED_EXACT_IMPORT_ROOT Hironaka' in (A / 'import-root-kernel-replay.log').read_text()
replayed = [line.removeprefix('replaying ') for line in (A / 'incremental-kernel-replay.log').read_text().splitlines()
    if line.startswith('replaying ')]
assert sorted(replayed) == sorted(load('new-module-targets.json')) == sorted(load('kernel-modules.json'))

bp = load('blueprint-validation.json')
expect(bp, status='PASS_COMPLETE_BLUEPRINT_LATEX_NO_ERRORS',
    native_accepted_checkpoint=CP, normal_published_revision=REV,
    complete_synchronized_chapters=399, complete_original_proofs=1560,
    distinct_local_bindings=4275, verified_upstream_only_bindings=241,
    explicit_historical_unresolved_bindings=2, distinct_synchronized_references=4518,
    new_chapters=9, new_complete_original_proofs=19, new_local_bindings=26,
    new_bindings_overlap_with_previous=0, all_document_chapters=484,
    all_document_complete_proof_environments=2031,
    all_document_distinct_local_binding_spellings=5434,
    all_inputs_exist_and_are_unique=True,
    all_475_preceding_document_input_sources_byte_identical=True,
    private_reference_derivatives_exported=False, pages=795, pdf_bytes=4007589,
    latex_errors=0, latex_warning_occurrences=704, reference_warning_occurrences=703,
    pdf_bookmark_warning_occurrences=6, missing_pdf_destination_warning_occurrences=72,
    math_environment_warning_occurrences=1,
    reference_warning_inventory_unchanged_from_predecessor=True,
    missing_pdf_destination_inventory_unchanged_from_predecessor=True,
    latex_passes=3, final_cross_references_stable=True,
    input_sources_unchanged_during_render=True)
assert digest(A / bp['pdf_path']) == bp['pdf_sha256']
assert digest(A / bp['input_source_digests_file']) == bp['input_source_digests_sha256']
input_digests = load(bp['input_source_digests_file'])
assert len(input_digests) == 485
for name, sha in input_digests.items():
    assert digest(ROOT / name) == sha

prior_path = PREVIOUS / 'all-actual-raw-structural-comparison-final.json'
assert json.loads(prior_path.read_text())['status'] == 'BLOCKED_EXACT_DIFFERENCE'
for path in [prior_path, PREVIOUS / 'final-validation.json']:
    assert subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':' + str(path.relative_to(ROOT))]) == path.read_bytes()
prior = json.loads((PREVIOUS / 'final-validation.json').read_text())
expect(prior, strict_complete_mathematical_types_and_values=1006,
    parser_frontend_definitions_separately_source_audited=3,
    parser_bodies_structural_equality_claimed=False,
    raw_all_actual_structural_status='BLOCKED_EXACT_DIFFERENCE')

readme = (ROOT / 'README.md').read_text()
assert readme == (A / 'README-next-checkpoint.md.txt').read_text()
assert '**Three of the nine original gaps are closed: G5, G6 and G7.**' in readme
assert '**Six broader gaps remain open:**' in readme
for gap in ['G1', 'G2', 'G3', 'G4', 'G8', 'G9']:
    assert f'| {gap} —' in readme
assert REV in readme and '322-module' in readme
assert 'BLOCKED_EXACT_DIFFERENCE' in readme
assert 'equality of those three bodies remains unclaimed' in readme
missing_links = []
for target in re.findall(r'\]\(([^)]+)\)', readme):
    if target.startswith('#') or re.match(r'\w+:', target):
        continue
    path = ROOT / unquote(target.split('#', 1)[0])
    if not path.exists() and path != A / 'final-validation.json':
        missing_links.append(target)
assert not missing_links, missing_links

evidence = ['published-source-replay.json', 'frozen-tool-profiles.json',
    'whole-module-full-expression-comparison.json', 'fragment-full-expression-comparison.json',
    'fragment-original-root-selection.json', 'all-actual-roots-final.log',
    'build-03-original-instance-context.log', 'recorded-full-expression-captures.json',
    'recorded-full-expression-replay.log', 'incremental-kernel-replay.json',
    'kernel-artifacts-before.json', 'kernel-artifacts-after.json',
    'previous-frozen-kernel-data-reuse.json', 'blueprint-validation.json',
    'blueprint-all-input-source-digests.json',
    'g3-original-support-and-context-review.json', 'original-instance-context-provenance.json',
    'owned-administrative-contexts.json', 'original-instance-restorations.json', 'verification.md', 'README-next-checkpoint.md.txt',
    'verify_incremental_source.py', 'verify_recorded_full_expressions.py',
    'restore_original_support.py', 'sync_frozen_322.py', 'prepare_readme_update.py',
    'validate_publication.py']
report = {
    'status': 'PASS_ALL_PUBLICATION_GATES_FIXED_322_INCREMENT',
    'normal_published_native_revision': REV, 'accepted_native_source_checkpoint': CP,
    'previous_public_main': BASE, 'accepted_native_continuation_modules': 322,
    'later_native_checkpoints_included': False,
    'mathematical_modules': 1015, 'all_local_modules_including_root': 1016,
    'all_actual_compiled_roots_standard_three_only': 16926,
    'new_modules': 13, 'whole_original_modules': 9,
    'pure_original_support_modules': 4, 'complete_original_support_declarations': 11,
    'new_actual_compiled_roots': 63, 'strict_complete_types_and_values': 63,
    'strict_complete_theorem_proofs': 59,
    'all_actual_private_and_generated_new_roots_strictly_compared': True,
    'new_parser_frontend_structural_differences': 0,
    'full_build_jobs': 5007, 'full_build_warnings': 0,
    'source_scope': source, 'frozen_kernel_coverage': kernel,
    'blueprint_source_and_pdf_scope': bp,
    'all_document_compiled_exact_local_bindings': 5434,
    'independent_entire_reviews': ['g3-original-support-and-context-review.json'],
    'previous_1002_mathematical_sources_byte_identical': True,
    'previous_1002_complete_kernel_artifacts_byte_identical': True,
    'original_declaration_type_proof_text_changes': 0,
    'new_administrative_original_instance_restorations': 1,
    'preceding_parser_disclosure': {
        'strict_math_roots': 1006, 'separately_typed_source_audited_frontend_definitions': 3,
        'raw_all_1009_structural_status': 'BLOCKED_EXACT_DIFFERENCE',
        'three_frontend_bodies_structural_equality_claimed': False,
        'preceding_verified_source_kernel_chain_reused': True},
    'closed_original_gaps': ['G5', 'G6', 'G7'],
    'general_original_gaps_still_open': ['G1', 'G2', 'G3', 'G4', 'G8', 'G9'],
    'full_hironaka_complete': False,
    'captured_expression_comparison_reproduced_from_lossless_gzip': True,
    'historical_failed_attempts_and_rejected_comparisons_retained': True,
    'fresh_full_library_kernel_replay_claimed': False,
    'current_artifact_sha256': {name: digest(A / name) for name in evidence},
    'readme_sha256': digest(ROOT / 'README.md'),
    'final_validation_method': 'Read-only current source, complete installed kernel/metadata artifact, captured-gate, portable lossless-capture and blueprint-input guards; no verification rerun is inferred from this receipt.'}
(A / 'final-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({key: value for key, value in report.items() if not isinstance(value, (dict, list))}))
