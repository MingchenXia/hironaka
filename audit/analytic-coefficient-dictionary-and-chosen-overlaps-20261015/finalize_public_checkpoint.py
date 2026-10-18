"""Assemble final public documentation only after every separate gate passes."""
from pathlib import Path
import hashlib
import json
import re
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
def load(name):
    return json.loads((HERE / name).read_text())

source = load('source-recovery-replay.json')
assert source['status'] == 'PASS_COMPLETE_SOURCE_TEXT_REPLAY_AND_OLD_SOURCE_GUARD'
assert source['whole_new_modules'] == 59 and source['new_module_targets'] == 81
assert source['old_mathematical_modules_byte_identical'] == 886
assert source['previous_source_exact_original_instance_import_repairs'] == ['Hironaka/Analytic/GeometricPureDimension.lean']
build = (HERE / 'build-29-final-whole-library.log').read_text()
assert 'Build completed successfully (4952 jobs).' in build
assert not re.search(r'(?im)^.*\bwarning:', build)
axioms = (HERE / 'public-all-actual-compiled-roots-after-prerequisite-repair.log').read_text()
for needle in ['ALL_LIBRARY_MODULES 969', 'ALL_LIBRARY_ACTUAL_ROOTS 16571',
               'NEW_MODULES 81', 'NEW_ACTUAL_ROOTS 1009', 'EXACT_BINDINGS 541',
               'SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4074',
               'ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5233', 'MISSING 0', 'STANDARD_THREE_ONLY']:
    assert needle in axioms, needle
classified = load('all-actual-root-verification-classification-final.json')
assert classified['strict_complete_type_and_value_roots_per_side'] == 1006
assert classified['mathematical_theorem_proofs_strict_exact'] == 839
assert classified['raw_all_actual_structural_status'] == 'BLOCKED_EXACT_DIFFERENCE'
assert not classified['three_parser_bodies_structural_equality_claimed']
parser = load('parser-typed-source-generation-final.json')
assert parser['status'] == 'PASS_REFRESHED_TYPED_SOURCE_GENERATION_GATE_WITH_INDEPENDENT_INITIAL_REVIEW'
isolation = load('parser-logical-isolation-final.json')
assert isolation['status'] == 'PASS_ACTUAL_COMPILER_TYPES_AND_NO_LOGICAL_CONSTANT_DEPENDENTS'
assert isolation['all_public_moduleData_modules'] == 969
assert isolation['all_public_moduleData_constants'] == 16571
assert isolation['other_actual_constants_scanned'] == 16568
assert isolation['direct_type_constant_edges_scanned'] == 605859
assert isolation['direct_entire_value_constant_edges_scanned'] == 1029586
assert isolation['direct_references_to_three_public_parser_roots'] == []
assert isolation['roots_excluded_from_kernel_or_axiom_inventory'] == 0
assert not isolation['parser_body_structural_equality_claimed']
for name, expected in parser['evidence_sha256'].items():
    assert hashlib.sha256((HERE / name).read_bytes()).hexdigest() == expected, name
kernel = load('incremental-kernel-replay.json')
assert kernel['status'] == 'PASS_ALL_NEW_MODULES_AND_REPAIRED_PREREQUISITE_CONE_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
assert kernel['new_modules'] == 81 and kernel['fresh_mathematical_modules'] == 426
assert kernel['previous_nonroot_modules_reused_from_identical_verified_checkpoint'] == 542
assert kernel['full_sources_and_kernel_parts_unchanged'] and kernel['import_root_replayed_with_installed_LeanChecker']
assert not kernel['fresh_full_library_replay_claimed']
assert load('kernel-artifacts-before.json') == load('kernel-artifacts-after.json')
bp = load('blueprint-source-scope-validation.json')
pdf = load('blueprint-pdf-validation-final.json')
assert bp['complete_synchronized_chapters'] == 357 and bp['all_document_chapters'] == 442
assert bp['all_document_distinct_local_binding_spellings'] == 5233 and pdf['pages'] == 750
assert pdf['latex_errors'] == 0 and not pdf['rerun_required']
assert 'PASS recorded complete mathematical types/values: 1006 roots, 839 theorem proofs.' in (HERE / 'recorded-full-expression-reproduction.log').read_text()
required = ['source-recovery-replay.json', 'source-replay-final-before-kernel.log',
    'build-29-final-whole-library.log', 'public-all-actual-compiled-roots-after-prerequisite-repair.log',
    'all-actual-root-verification-classification-final.json', 'all-mathematical-strict-comparison-final.json',
    'all-actual-raw-structural-comparison-final.json', 'parser-typed-source-generation-final.json',
    'parser-logical-isolation-final.json', 'g3-parser-typed-source-generation-final-review.md',
    'g3-parser-typed-source-generation-final-review.json', 'g3-classification-and-frozen-coverage-tool-review.md',
    'g3-classification-and-frozen-coverage-tool-review.json', 'g3-original-cstar-context-delta-review.json',
    'incremental-kernel-replay.json', 'incremental-kernel-replay.log', 'import-root-kernel-replay.log',
    'kernel-artifacts-before.json', 'kernel-artifacts-after.json', 'previous-frozen-kernel-data-reuse.json',
    'kernel-modules.json', 'blueprint-source-scope-validation.json', 'blueprint-pdf-validation-final.json',
    'blueprint-all-input-source-digests.json', 'original-instance-context-final-receipt.json',
    'original-cstar-prerequisite-context-repair.json', 'original-cstar-compiler-import-chain.json',
    'lossless-expression-snapshot-compression.json', 'recorded-full-expression-reproduction.log',
    'compare_classified_actual_roots.py', 'verify_recorded_full_expressions.py',
    'verify_incremental_source.py', 'verify_final_parser_source_generation.py',
    'snapshot_kernel_artifacts.py', 'validate_previous_reuse.py',
    'prepare_frozen_kernel_coverage.py', 'run_incremental_kernel_replay.py']
hashes = {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in required}
report = {
    'status': 'PASS_PUBLIC_CHECKPOINT_WITH_SEPARATE_DISCLOSED_PARSER_SOURCE_GENERATION_GATE',
    'normal_published_native_revision': source['published_native_revision'],
    'accepted_native_source_checkpoint': source['native_frozen_revision'],
    'mathematical_modules': 968, 'all_local_modules_including_root': 969,
    'all_actual_compiled_roots_standard_three_only': 16571,
    'new_modules': 81, 'new_actual_compiled_roots': 1009,
    'strict_complete_mathematical_types_and_values': 1006,
    'strict_complete_theorem_proofs': 839,
    'all_private_and_generated_mathematical_roots_strictly_compared': True,
    'parser_frontend_definitions_separately_source_audited': 3,
    'parser_bodies_structural_equality_claimed': False,
    'raw_all_actual_structural_status': 'BLOCKED_EXACT_DIFFERENCE',
    'full_build_jobs': 4952, 'full_build_warnings': 0,
    'source_scope': source, 'frozen_kernel_coverage': kernel,
    'blueprint_source_scope': bp, 'blueprint_pdf': pdf,
    'all_document_compiled_exact_local_bindings': 5233,
    'closed_original_gaps': ['G5', 'G6', 'G7'],
    'general_original_gaps_still_open': ['G1', 'G2', 'G3', 'G4', 'G8', 'G9'],
    'full_hironaka_complete': False,
    'independent_entire_reviews': [name for name in required if name.startswith('g3-')],
    'current_artifact_sha256': hashes,
    'historical_failed_attempts_and_rejected_comparisons_retained': True,
    'captured_expression_comparison_reproduced_from_lossless_gzip': True,
    'fresh_full_library_kernel_replay_claimed': False}
(HERE / 'final-validation.json').write_text(json.dumps(report, indent=2) + '\n')
(HERE / 'verification.md').write_text('''# Analytic coefficient dictionary and chosen curve overlaps

The frozen native 280-module continuation is synchronized from normal published upstream revision `09dc511c4a14836a0287748d1a63f9f467f677d3`. This increment contains 59 whole original modules, 22 pure support modules retaining 58 complete original declarations, eight reused original support declarations and 38 complete blueprint chapters. It supplies genuine analytic relative coefficient germs and their literal Taylor dictionary, original StepOne and prepared companion geometry, and topological gluing from already chosen local curve overlap maps. Later native checkpoints are not included.

The full public library builds in 4,952 jobs with zero warnings. ALL 16,571 actual roots, including private/generated declarations and the three parser definitions below, use only the standard three axioms. Every one of the full document's 5,233 distinct local Lean bindings resolves in the actual compiled library.

The unchanged strict comparator checks ALL 1,006 new mathematical roots and 839 complete theorem proofs. Complete types, values, private/generated helpers, numerical names, binders and metadata match, without alpha/definitional comparison or erasure. Exactly three actual frontend definitions generated by unchanged original local notation (parser descriptor, macro and unexpander) differ in generated relocation names and quoted hygiene identifiers. The raw all-1,009-root comparison remains honestly BLOCKED on these records. A separate independently reviewed typed source-generation gate replays their unchanged original source. An actual environment traversal finds zero references to them from any of the other 16,568 roots. Their bodies are retained losslessly and their structural equality is not claimed.

Source replay preserves 886 preceding mathematical files byte for byte. Exactly one preceding prerequisite receives its genuine original CStar Mathlib import, restoring the original scalar-topology context in a reused definition. No declaration or proof text is changed. Fresh kernel replay covers all 81 new modules, ALL 345 preceding modules in the actual compiler dependency cone of that repair, and the import root. The other 542 modules have byte-identical sources and every kernel-data part relative to the pinned verified predecessor. Before/after snapshots also pin compiled import metadata. This covers all 969 modules by a recorded chain, rather than claiming a fresh full-library replay.

The blueprint contains 357 synchronized complete chapters, 1,465 complete proofs and 4,074 distinct local bindings, with 241 verified upstream-only bindings and two explicitly unresolved historical names. Including earlier original extension chapters gives 442 inputs, 1,936 proof environments and 5,233 distinct local bindings. Its 750-page PDF renders without LaTeX errors. Historical external-reference and bookmark warnings remain disclosed in raw logs and the PDF receipt; successful rendering does not establish those external targets.

See [final-validation.json](final-validation.json) for exact artifact hashes and separate source, expression, parser, axiom, kernel, blueprint and independent review receipts. `verify_incremental_source.py --source-root /path/to/archon-nakamaye` reproduces source recovery from normal published Git. `verify_recorded_full_expressions.py` decodes lossless snapshots and reruns the unchanged classifier/comparator, including the expected raw parser difference. Captured-data reproduction is distinct from checking a current Lean environment.

G5, G6 and G7 are closed. G1, G2, G3, G4, G8 and G9 retain their general goals. This snapshot does not claim arbitrary formal convergence, the complete higher-dimensional canonical endpoint, full analytic geometric descent, a general globally scheduled noncompact blowup history, or full Hilbert–Samuel transformation/Bennett inequalities. Earlier failed context repairs, raw structural failures and the rejected parser-normalization prototype remain as evidence.
''')
shutil.copyfile(HERE / 'README-proposal.md', ROOT / 'README.md')
print('PASS final separate gates; README and final report updated.')
