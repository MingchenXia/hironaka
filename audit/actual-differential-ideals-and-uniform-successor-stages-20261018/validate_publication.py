"""Validate fixed346's separate gates and current source/kernel/input hashes.

This launches no Lean, build, export, kernel replay or network.
"""
from pathlib import Path
import hashlib,json,re,subprocess
from urllib.parse import unquote
from validate_previous_reuse import validate_reuse
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='958de4f86cd3cbabcd581f86ac1a9d55265fb39b';REV='a69bc11bac55579b74fa4db4eac2740a93000f85';CP='d62f9c5aae6e0b4ca81f8c484b48edae998c154f'
load=lambda n:json.loads((A/n).read_text())
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as src:
  for block in iter(lambda:src.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def expect(r,**fields):
 for k,v in fields.items():assert r[k]==v,(k,r[k],v)
source=load('published-source-replay.json')
expect(source,status='PASS_COMPLETE_NORMAL_PUBLISHED_SOURCE_REPLAY_AND_1034_PREVIOUS_SOURCE_GUARD',accepted_native_checkpoint=CP,normal_published_revision=REV,previous_public_main=BASE,previous_mathematical_sources_byte_identical=1034,whole_original_modules=8,original_pure_support_modules=0,complete_original_support_declarations=0,complete_blueprint_chapters=8,complete_original_blueprint_proofs=19,complete_blueprint_labelled_nodes=23,labelled_definition_without_proof=4,every_labelled_nondefinition_has_complete_proof=True,local_blueprint_bindings=43,new_module_targets=8,root_changes_only_recorded_imports=4,private_ledger_required=False,original_type_proof_text_changes=0,frozen_tool_profiles_unchanged=True)
provenance=load('provenance.json');assert len(provenance)==8
for r in provenance:
 assert not r['administrative_elaboration_contexts'] and not r['additional_pure_support_imports']
 assert r['initial_synchronized_destination_sha256']==r['destination_sha256']==digest(ROOT/(r['destination_module'].replace('.','/')+'.lean'))
for r in load('frozen-tool-profiles.json'):assert digest(ROOT/r['path'])==r['sha256']
whole=load('whole-module-full-expression-comparison.json')
expect(whole,status='EXACT_ALL_FULL_EXPR_DAG_MATCH',missing=[],native_extras=[],approved_native_extras=[],unapproved_native_extras=[],differences=[],fallbacks=0,auxiliaries_skipped=0,proof_numbers_erased=0,binder_names_erased=0,defeq_or_alpha_comparison=False,metadata_preserved_in_full=True)
assert whole['old']['all_actual_constants']==whole['native']['all_actual_constants']==108
assert len(whole['module_counts'])==8 and sum(v['constants'] for v in whole['module_counts'].values())==108 and sum(v['theorems'] for v in whole['module_counts'].values())==66
for v in whole['module_counts'].values():assert v['constants']==v['types_exact']==v['values_exact'] and v['theorems']==v['theorem_proofs_exact']
assert whole['comparator']['sha256']==digest(ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py')
captures={r['path']:r for r in load('recorded-full-expression-captures.json')};assert set(captures)=={'native-full-expressions.jsonl','public-full-expressions.jsonl'}
for r in captures.values():assert digest(A/r['gzip_path'])==r['gzip_sha256'] and (A/r['gzip_path']).stat().st_size==r['gzip_bytes']
for side in ['old','native']:assert captures[Path(whole[side]['path']).name]['sha256']==whole[side]['sha256']
assert 'PASS_ALL_108_RECORDED_ACTUAL_ROOTS_AND_66_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON' in (A/'recorded-full-expression-replay.log').read_text()
build=(A/'build-01-frozen-original-whole.log').read_text();assert 'Build completed successfully (5035 jobs).' in build and not re.search(r'(?im)^.*\b(?:warning|error):',build)
compiled=(A/'all-actual-roots-final.log').read_text()
for marker in ['ALL_LIBRARY_MODULES 1043; ALL_LIBRARY_ACTUAL_ROOTS 17277; NEW_MODULES 8; NEW_ACTUAL_ROOTS 108; EXACT_BINDINGS 43; MISSING 0; STANDARD_THREE_ONLY','SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4378; MISSING 0','ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5537; MISSING 0']:assert marker in compiled
for name,n in [('new-local-bindings.json',43),('complete-blueprint-local-bindings.json',4378),('all-document-local-bindings.json',5537)]:assert len(load(name))==len(set(load(name)))==n
peer=load('g3-original-whole-source-and-scope-review.json')
expect(peer,status='PASS_INDEPENDENT_ENTIRE_WHOLE_SOURCE_FIDELITY_AND_PRODUCER_SCOPE_REVIEW',normal_published_revision=REV,accepted_native_checkpoint=CP,whole_module_count=8,new_supports=0,administrative_import_or_TC_changes=0,complete_blueprint_chapters=8,complete_proofs=19,labelled_nodes=23,definitions=5,local_bindings=43,heavy_checks_repeated=False)
assert set(peer['definition_labels_without_artificial_proof'])=={'hir:actual-original-differential-ideal-definition','hir:actual-original-iterated-differential-ideal-definition','hir:original-finite-level-cut-history','hir:sharp-actual-curve-uniform-successor-data'}
for r in peer['whole_modules']:
 own=next(v for v in provenance if v['destination_module']==r['module']);assert own['source_sha256']==r['source_sha256'] and own['destination_sha256']==r['destination_sha256']
for name,h in peer['file_sha256'].items():assert digest(A/name)==h,name
if 'readme_sha256' in peer:assert digest(ROOT/'README.md')==peer['readme_sha256'] and digest(A/'prepare_readme_update.py')==peer['readme_generator_sha256']
if 'observed_final_strict_gates' in peer:
 for name,r in peer['observed_final_strict_gates'].items():assert digest(A/name)==r['sha256']
before=load('kernel-artifacts-before.json');after=load('kernel-artifacts-after.json');assert before==after
assert after['mathematical_modules_including_root']==after['kernel_data_parts']==1043
assert set(after['sources'])=={'Hironaka.lean'}|{str(p.relative_to(ROOT)) for p in (ROOT/'Hironaka').rglob('*.lean')}
for category in ['sources','compiled_kernel_data_parts','compiled_import_metadata_sha256']:
 for name,h in after[category].items():assert digest(ROOT/name)==h,(category,name)
reuse=validate_reuse(A,after)
expect(reuse,reused_preceding_modules=1034,fresh_new_modules=8,fresh_additional_changed_previous_kernel_modules=0,fresh_mathematical_modules=8,all_1034_previous_mathematical_sources_byte_identical=True)
kernel=load('incremental-kernel-replay.json')
expect(kernel,status='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY',new_modules=8,fresh_mathematical_modules=8,new_module_exact_inventory=True,import_root_replayed_with_installed_LeanChecker=True,full_sources_and_kernel_parts_unchanged=True,total_local_modules=1043,total_kernel_parts=1043,previous_nonroot_modules_reused_from_identical_verified_checkpoint=1034,lean_num_threads=1,fresh_full_library_replay_claimed=False)
assert 'REPLAYED_EXACT_IMPORT_ROOT Hironaka' in (A/'import-root-kernel-replay.log').read_text()
observed=[line.removeprefix('replaying ') for line in (A/'incremental-kernel-replay.log').read_text().splitlines() if line.startswith('replaying ')];assert sorted(observed)==sorted(load('new-module-targets.json'))==sorted(load('kernel-modules.json'))
native_bp=load('accepted-native-blueprint-scope-validation.json')
expect(native_bp,status='PASS_ALL_346_NATIVE_CHAPTERS_LABELLED_STATEMENTS_PROOFS_AND_DEFINITIONS',normal_published_revision=REV,accepted_native_source_checkpoint=CP,chapters=346,labelled_nodes=1065,complete_nonempty_proof_environments=1059,labelled_definition_nodes=34,labelled_definitions_without_proof=6,every_labelled_nondefinition_has_complete_proof=True,labelled_nondefinitions=1031,definition_proofs_manufactured=0,private_ledger_required=False)
expect(load('blueprint-new-statement-proof-scope.json'),status='PASS_EVERY_LABELLED_NONDEFINITION_HAS_COMPLETE_PROOF',labelled_nodes=23,complete_proofs=19,definition_nodes=5,definition_without_proof=4)
bp=load('blueprint-validation.json')
expect(bp,status='PASS_COMPLETE_BLUEPRINT_LATEX_NO_ERRORS',native_accepted_checkpoint=CP,normal_published_revision=REV,complete_synchronized_chapters=423,complete_original_proofs=1612,distinct_local_bindings=4378,verified_upstream_only_bindings=241,explicit_historical_unresolved_bindings=2,distinct_synchronized_references=4621,new_chapters=8,new_complete_original_proofs=19,new_local_bindings=43,new_bindings_overlap_with_previous=0,new_labelled_statement_nodes=23,new_labelled_nondefinitions_with_complete_proofs=18,new_labelled_definitions_without_proof=4,new_definition_proofs_manufactured=0,all_document_chapters=508,all_document_complete_proof_environments=2083,all_document_distinct_local_binding_spellings=5537,all_inputs_exist_and_are_unique=True,all_500_preceding_document_input_sources_byte_identical=True,private_reference_derivatives_exported=False,pages=821,pdf_bytes=4118312,latex_errors=0,latex_warning_occurrences=704,reference_warning_occurrences=703,pdf_bookmark_warning_occurrences=6,missing_pdf_destination_warning_occurrences=72,math_environment_warning_occurrences=1,reference_warning_inventory_unchanged_from_predecessor=True,missing_pdf_destination_inventory_unchanged_from_predecessor=True,latex_passes=3,final_cross_references_stable=True,input_sources_unchanged_during_render=True)
assert digest(A/bp['pdf_path'])==bp['pdf_sha256'] and digest(A/bp['input_source_digests_file'])==bp['input_source_digests_sha256']
inputs=load(bp['input_source_digests_file']);assert len(inputs)==509
for name,h in inputs.items():assert digest(ROOT/name)==h
assert len(load('master-documentation-contexts.json'))==1
legacy=A.parent/'analytic-coefficient-dictionary-and-chosen-overlaps-20261015'
for name in ['all-actual-raw-structural-comparison-final.json','final-validation.json']:
 path=legacy/name;assert subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+str(path.relative_to(ROOT))])==path.read_bytes()
assert json.loads((legacy/'all-actual-raw-structural-comparison-final.json').read_text())['status']=='BLOCKED_EXACT_DIFFERENCE'
expect(json.loads((legacy/'final-validation.json').read_text()),strict_complete_mathematical_types_and_values=1006,parser_frontend_definitions_separately_source_audited=3,parser_bodies_structural_equality_claimed=False,raw_all_actual_structural_status='BLOCKED_EXACT_DIFFERENCE')
readme=(ROOT/'README.md').read_text();assert readme==(A/'README-next-checkpoint.md.txt').read_text()
for phrase in ['**Three of the nine original gaps are closed: G5, G6 and G7.**','**Six broader gaps remain open:**',REV,'346-module','same given Cartesian source history','without prefix canonicity','General numerical FULL compatibility along arbitrary histories','Global descent of successive arrows and centres','all finite differential closures','BLOCKED_EXACT_DIFFERENCE','equality of those three bodies remains unclaimed']:assert phrase in readme,phrase
for path in [ROOT/'README.md',A/'verification.md']:
 for target in re.findall(r'\]\(([^)]+)\)',path.read_text()):
  if target.startswith('#') or re.match(r'\w+:',target):continue
  dest=path.parent/unquote(target.split('#',1)[0]);assert dest.exists() or dest==A/'final-validation.json',(path,target)
evidence=[p for p in sorted(A.iterdir()) if p.is_file() and p.name not in ['final-validation.json','final-validation.log'] and not p.name.endswith('.jsonl')]
report={'status':'PASS_ALL_PUBLICATION_GATES_FIXED_346_INCREMENT','normal_published_native_revision':REV,'accepted_native_source_checkpoint':CP,'native_project_tree':'b6d24efe6dcba0c5cf9382d370c110b65dc9589e','previous_public_main':BASE,'accepted_native_continuation_modules':346,'later_native_checkpoints_included':False,'mathematical_modules':1042,'all_local_modules_including_root':1043,'all_actual_compiled_roots_standard_three_only':17277,'new_whole_modules':8,'new_support_modules':0,'new_actual_compiled_roots':108,'strict_complete_types_and_values':108,'strict_complete_theorem_proofs':66,'all_new_actual_private_and_generated_roots_strictly_compared':True,'new_parser_frontend_structural_differences':0,'new_whole_source_import_adjustments':0,'new_whole_instance_context_adjustments':0,'original_type_proof_text_changes':0,'full_build_jobs':5035,'full_build_warnings':0,'source_scope':source,'frozen_kernel_coverage':kernel,'accepted_native_blueprint_statement_scope':native_bp,'blueprint_source_and_pdf_scope':bp,'all_document_compiled_exact_local_bindings':5537,'independent_entire_source_and_scope_review':'g3-original-whole-source-and-scope-review.json','previous_1034_mathematical_sources_byte_identical':True,'previous_1034_complete_kernel_artifacts_byte_identical':True,'legacy_parser_disclosure':{'strict_math_roots':1006,'separately_source_audited_frontend_definitions':3,'raw_all_1009_structural_status':'BLOCKED_EXACT_DIFFERENCE','three_frontend_bodies_equality_claimed':False},'closed_original_gaps':['G5','G6','G7'],'general_original_gaps_still_open':['G1','G2','G3','G4','G8','G9'],'actual_proper_global_uniform_stages_complete':True,'global_successor_arrow_and_centre_descent_claimed_complete':False,'finite_cut_lower_geometry_and_earlier_mask_avoidance_without_CAN_complete':True,'general_arbitrary_history_FULL_value_compatibility_claimed_complete':False,'whole_Taylor_derivative_and_all_finite_differential_closure_extension_complete':True,'full_hironaka_complete':False,'fresh_full_library_kernel_replay_claimed':False,'captured_full_expression_comparison_reproduced_from_lossless_gzip':True,'historical_evidence_preserved':True,'current_artifact_sha256':{p.name:digest(p) for p in evidence},'pdf_sha256':digest(A/bp['pdf_path']),'readme_sha256':digest(ROOT/'README.md'),'final_validation_method':'Read-only current source/kernel/import-metadata/input/capture/receipt guards; separate Lean, complete-expression and installed kernel gates are not inferred or rerun.'}
(A/'final-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if not isinstance(v,(dict,list))}))
