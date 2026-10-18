"""Validate fixed333's gates and current source/kernel/input/capture hashes.

No Lean, build, export, kernel replay or network is launched by this validator.
"""
from pathlib import Path
import hashlib,json,re,subprocess
from urllib.parse import unquote
from validate_previous_reuse import validate_reuse
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='f7985b63b43a2423dfbf09b3eef4e487330dde1d'
REV='d9c39cb76c09fb9c5c92936fb96d61e8547c08b3'
CP='429ae0ee718cdae5faace3f7aecb6eedf23bb81e'
load=lambda name:json.loads((A/name).read_text())
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def expect(record,**fields):
 for key,value in fields.items():assert record[key]==value,(key,record[key],value)

source=load('published-source-replay.json')
expect(source,status='PASS_COMPLETE_NORMAL_PUBLISHED_SOURCE_REPLAY_AND_1015_PREVIOUS_SOURCE_GUARD',
 accepted_native_checkpoint=CP,normal_published_revision=REV,previous_public_main=BASE,
 previous_mathematical_sources_byte_identical=1015,whole_original_modules=11,
 original_pure_support_modules=0,complete_original_support_declarations=0,
 complete_blueprint_chapters=11,complete_original_blueprint_proofs=21,
 complete_blueprint_labelled_nodes=22,labelled_definition_without_proof=1,
 every_labelled_nondefinition_has_complete_proof=True,local_blueprint_bindings=38,
 new_module_targets=11,root_changes_only_recorded_imports=4,private_ledger_required=False,
 original_type_proof_text_changes=0,frozen_tool_profiles_unchanged=True)
provenance=load('provenance.json');assert len(provenance)==11
for record in provenance:
 assert not record['administrative_elaboration_contexts'] and not record['additional_pure_support_imports']
 assert digest(ROOT/(record['destination_module'].replace('.','/')+'.lean'))==record['destination_sha256']
for record in load('frozen-tool-profiles.json'):
 assert digest(ROOT/record['path'])==record['sha256']
whole=load('whole-module-full-expression-comparison.json')
expect(whole,status='EXACT_ALL_FULL_EXPR_DAG_MATCH',missing=[],native_extras=[],
 approved_native_extras=[],unapproved_native_extras=[],differences=[],fallbacks=0,
 auxiliaries_skipped=0,proof_numbers_erased=0,binder_names_erased=0,
 defeq_or_alpha_comparison=False,metadata_preserved_in_full=True)
assert whole['old']['all_actual_constants']==whole['native']['all_actual_constants']==148
assert len(whole['module_counts'])==11
assert sum(r['constants'] for r in whole['module_counts'].values())==148
assert sum(r['theorems'] for r in whole['module_counts'].values())==109
for record in whole['module_counts'].values():
 assert record['constants']==record['types_exact']==record['values_exact']
 assert record['theorems']==record['theorem_proofs_exact']
assert whole['comparator']['sha256']==digest(ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py')
captures={r['path']:r for r in load('recorded-full-expression-captures.json')}
assert set(captures)=={'native-full-expressions.jsonl','public-full-expressions.jsonl'}
for record in captures.values():
 assert digest(A/record['gzip_path'])==record['gzip_sha256']
 assert (A/record['gzip_path']).stat().st_size==record['gzip_bytes']
for side in ['old','native']:
 assert captures[Path(whole[side]['path']).name]['sha256']==whole[side]['sha256']
assert 'PASS_ALL_148_RECORDED_ACTUAL_ROOTS_AND_109_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON' in (A/'recorded-full-expression-replay.log').read_text()
build=(A/'build-01-frozen-original-whole.log').read_text()
assert 'Build completed successfully (5018 jobs).' in build
assert not re.search(r'(?im)^.*\b(?:warning|error):',build)
actual=(A/'all-actual-roots-final.log').read_text()
assert 'ALL_LIBRARY_MODULES 1027; ALL_LIBRARY_ACTUAL_ROOTS 17074; NEW_MODULES 11; NEW_ACTUAL_ROOTS 148; EXACT_BINDINGS 38; MISSING 0; STANDARD_THREE_ONLY' in actual
assert 'SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4313; MISSING 0' in actual
assert 'ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5472; MISSING 0' in actual
for name,count in [('new-local-bindings.json',38),('complete-blueprint-local-bindings.json',4313),('all-document-local-bindings.json',5472)]:
 bindings=load(name);assert len(bindings)==len(set(bindings))==count

peer=load('g3-original-whole-source-and-scope-review.json')
expect(peer,status='PASS_INDEPENDENT_WHOLE_SOURCE_FIDELITY_AND_SCOPE_REVIEW',
 normal_published_revision=REV,accepted_native_checkpoint=CP,whole_modules_count=11,
 new_supports=0,whole_math_administrative_adjustments=0,complete_blueprint_chapters=11,
 complete_original_proofs=21,labelled_nodes=22,new_exact_local_bindings=38,
 old_source_guard_observed=1015,heavy_checks_repeated=False)
assert peer['definition_without_artificial_proof']==['hir:actual-analytic-normalized-member-ideal']
for record in peer['whole_modules']:
 assert record['whole_normal_git_canonical_copy_exact']
 own=next(r for r in provenance if r['destination_module']==record['module'])
 assert own['source_sha256']==record['source_sha256']
 assert digest(ROOT/(record['module'].replace('.','/')+'.lean'))==record['destination_sha256']
for name,sha in peer['file_sha256'].items():assert digest(A/name)==sha,name

before=load('kernel-artifacts-before.json');after=load('kernel-artifacts-after.json');assert before==after
assert after['mathematical_modules_including_root']==after['kernel_data_parts']==1027
sources={'Hironaka.lean'}|{str(p.relative_to(ROOT)) for p in (ROOT/'Hironaka').rglob('*.lean')}
assert sources==set(after['sources'])
for category in ['sources','compiled_kernel_data_parts','compiled_import_metadata_sha256']:
 for name,sha in after[category].items():assert digest(ROOT/name)==sha,(category,name)
reuse=validate_reuse(A,after)
expect(reuse,reused_preceding_modules=1015,fresh_new_modules=11,
 fresh_additional_changed_previous_kernel_modules=0,fresh_mathematical_modules=11,
 all_1015_previous_mathematical_sources_byte_identical=True)
kernel=load('incremental-kernel-replay.json')
expect(kernel,status='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY',
 new_modules=11,fresh_mathematical_modules=11,new_module_exact_inventory=True,
 import_root_replayed_with_installed_LeanChecker=True,full_sources_and_kernel_parts_unchanged=True,
 total_local_modules=1027,total_kernel_parts=1027,
 previous_nonroot_modules_reused_from_identical_verified_checkpoint=1015,
 lean_num_threads=1,fresh_full_library_replay_claimed=False)
assert 'REPLAYED_EXACT_IMPORT_ROOT Hironaka' in (A/'import-root-kernel-replay.log').read_text()
replayed=[s.removeprefix('replaying ') for s in (A/'incremental-kernel-replay.log').read_text().splitlines() if s.startswith('replaying ')]
assert sorted(replayed)==sorted(load('new-module-targets.json'))==sorted(load('kernel-modules.json'))

native_bp=load('accepted-native-blueprint-scope-validation.json')
expect(native_bp,status='PASS_ALL_333_NATIVE_CHAPTERS_LABELLED_STATEMENTS_PROOFS_AND_DEFINITIONS',
 normal_published_revision=REV,accepted_native_source_checkpoint=CP,chapters=333,
 labelled_nodes=1029,complete_nonempty_proof_environments=1028,labelled_definition_nodes=28,
 labelled_definitions_without_proof=1,every_labelled_nondefinition_has_complete_proof=True,
 labelled_nondefinitions=1001,definition_proofs_manufactured=0,private_ledger_required=False)
new_scope=load('blueprint-new-statement-proof-scope.json')
expect(new_scope,status='PASS_EVERY_LABELLED_NONDEFINITION_HAS_COMPLETE_PROOF',
 labelled_nodes=22,complete_proofs=21,definition_nodes=1,definition_without_proof=1)
bp=load('blueprint-validation.json')
expect(bp,status='PASS_COMPLETE_BLUEPRINT_LATEX_NO_ERRORS',native_accepted_checkpoint=CP,
 normal_published_revision=REV,complete_synchronized_chapters=410,complete_original_proofs=1581,
 distinct_local_bindings=4313,verified_upstream_only_bindings=241,explicit_historical_unresolved_bindings=2,
 distinct_synchronized_references=4556,new_chapters=11,new_complete_original_proofs=21,new_local_bindings=38,
 new_bindings_overlap_with_previous=0,new_labelled_statement_nodes=22,
 new_labelled_nondefinitions_with_complete_proofs=21,new_labelled_definitions_without_proof=1,
 new_definition_proofs_manufactured=0,all_document_chapters=495,
 all_document_complete_proof_environments=2052,all_document_distinct_local_binding_spellings=5472,
 all_inputs_exist_and_are_unique=True,all_484_preceding_document_input_sources_byte_identical=True,
 private_reference_derivatives_exported=False,pages=806,pdf_bytes=4055621,latex_errors=0,
 latex_warning_occurrences=704,reference_warning_occurrences=703,pdf_bookmark_warning_occurrences=6,
 missing_pdf_destination_warning_occurrences=72,math_environment_warning_occurrences=1,
 reference_warning_inventory_unchanged_from_predecessor=True,
 missing_pdf_destination_inventory_unchanged_from_predecessor=True,
 latex_passes=3,final_cross_references_stable=True,input_sources_unchanged_during_render=True)
assert digest(A/bp['pdf_path'])==bp['pdf_sha256']
assert digest(A/bp['input_source_digests_file'])==bp['input_source_digests_sha256']
inputs=load(bp['input_source_digests_file']);assert len(inputs)==496
for name,sha in inputs.items():assert digest(ROOT/name)==sha
assert 'Undefined control sequence.' in (A/'blueprint-pass-1-initial-deglex-undefined.log').read_text()
assert len(load('master-documentation-contexts.json'))==2

legacy=A.parent/'analytic-coefficient-dictionary-and-chosen-overlaps-20261015'
for name in ['all-actual-raw-structural-comparison-final.json','final-validation.json']:
 path=legacy/name;assert subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+str(path.relative_to(ROOT))])==path.read_bytes()
assert json.loads((legacy/'all-actual-raw-structural-comparison-final.json').read_text())['status']=='BLOCKED_EXACT_DIFFERENCE'
expect(json.loads((legacy/'final-validation.json').read_text()),strict_complete_mathematical_types_and_values=1006,
 parser_frontend_definitions_separately_source_audited=3,parser_bodies_structural_equality_claimed=False,
 raw_all_actual_structural_status='BLOCKED_EXACT_DIFFERENCE')
readme=(ROOT/'README.md').read_text();assert readme==(A/'README-next-checkpoint.md.txt').read_text()
for phrase in ['**Three of the nine original gaps are closed: G5, G6 and G7.**',
 '**Six broader gaps remain open:**',REV,'333-module','formal centre-power premise remains',
 'This public333 snapshot excludes','single global intermediate blowup schedule',
 'BLOCKED_EXACT_DIFFERENCE','equality of those three bodies remains unclaimed']:
 assert phrase in readme,phrase
for path in [ROOT/'README.md',A/'verification.md']:
 for target in re.findall(r'\]\(([^)]+)\)',path.read_text()):
  if target.startswith('#') or re.match(r'\w+:',target):continue
  dest=path.parent/unquote(target.split('#',1)[0])
  assert dest.exists() or dest==A/'final-validation.json',(path,target)
evidence=['published-source-replay.json','provenance.json','blueprint-provenance.json',
 'frozen-tool-profiles.json','whole-module-full-expression-comparison.json','all-actual-roots-final.log',
 'build-01-frozen-original-whole.log','recorded-full-expression-captures.json','recorded-full-expression-replay.log',
 'incremental-kernel-replay.json','kernel-artifacts-before.json','kernel-artifacts-after.json',
 'previous-frozen-kernel-data-reuse.json','blueprint-validation.json','blueprint-all-input-source-digests.json',
 'accepted-native-333-blueprint-records.json','accepted-native-blueprint-scope-validation.json',
 'blueprint-new-statement-proof-scope.json','g3-original-whole-source-and-scope-review.json',
 'master-documentation-contexts.json','verification.md','README-next-checkpoint.md.txt',
 'sync_frozen_333.py','verify_incremental_source.py','blueprint_statement_scope.py',
 'audit_native_accepted_blueprints.py','audit_complete_blueprint.py','verify_recorded_full_expressions.py',
 'prepare_readme_update.py','validate_publication.py']
report={'status':'PASS_ALL_PUBLICATION_GATES_FIXED_333_INCREMENT',
 'normal_published_native_revision':REV,'accepted_native_source_checkpoint':CP,
 'native_project_tree':'fa6233dc79005baf7ce7841262e67ead2d7616f9','previous_public_main':BASE,
 'accepted_native_continuation_modules':333,'later_native_checkpoints_included':False,
 'mathematical_modules':1026,'all_local_modules_including_root':1027,
 'all_actual_compiled_roots_standard_three_only':17074,'new_whole_modules':11,'new_support_modules':0,
 'new_actual_compiled_roots':148,'strict_complete_types_and_values':148,'strict_complete_theorem_proofs':109,
 'all_new_actual_private_and_generated_roots_strictly_compared':True,'new_parser_frontend_structural_differences':0,
 'new_whole_source_import_or_instance_context_adjustments':0,'original_type_proof_text_changes':0,
 'full_build_jobs':5018,'full_build_warnings':0,'source_scope':source,
 'frozen_kernel_coverage':kernel,'accepted_native_blueprint_statement_scope':native_bp,
 'blueprint_source_and_pdf_scope':bp,'all_document_compiled_exact_local_bindings':5472,
 'independent_entire_source_and_scope_review':'g3-original-whole-source-and-scope-review.json',
 'previous_1015_mathematical_sources_byte_identical':True,'previous_1015_complete_kernel_artifacts_byte_identical':True,
 'legacy_parser_disclosure':{'strict_math_roots':1006,'separately_source_audited_frontend_definitions':3,
  'raw_all_1009_structural_status':'BLOCKED_EXACT_DIFFERENCE','three_frontend_bodies_equality_claimed':False},
 'closed_original_gaps':['G5','G6','G7'],'general_original_gaps_still_open':['G1','G2','G3','G4','G8','G9'],
 'subsequent_native_prepared_comparison_progress_excluded_from_public333':True,
 'full_hironaka_complete':False,'fresh_full_library_kernel_replay_claimed':False,
 'captured_full_expression_comparison_reproduced_from_lossless_gzip':True,
 'initial_failed_pdf_attempt_retained':True,'historical_evidence_preserved':True,
 'current_artifact_sha256':{name:digest(A/name) for name in evidence},'readme_sha256':digest(ROOT/'README.md'),
 'final_validation_method':'Read-only current source/kernel/import-metadata/input/capture/receipt guards; separate recorded Lean, complete-expression and installed kernel gates are not inferred or rerun.'}
(A/'final-validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if not isinstance(v,(list,dict))}))
