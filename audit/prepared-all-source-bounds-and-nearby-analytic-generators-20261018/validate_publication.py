"""Validate fixed338 receipts and current source/kernel/input/capture hashes.

No Lean, build, export, kernel replay or network is launched here.
"""
from pathlib import Path
import hashlib,json,re,subprocess
from urllib.parse import unquote
from validate_previous_reuse import validate_reuse
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='2342eead0cdd7bba08acb2456e275a916bab94cf'
REV='f873b1d904f8e63cd9f73e0b5bf6eefb0332093a'
CP='862e555f2c5289f9b29cb844461cda7a23618d7c'
load=lambda n:json.loads((A/n).read_text())
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as stream:
  for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def expect(r,**fields):
 for k,v in fields.items():assert r[k]==v,(k,r[k],v)
source=load('published-source-replay.json')
expect(source,status='PASS_COMPLETE_NORMAL_PUBLISHED_SOURCE_REPLAY_AND_1026_PREVIOUS_SOURCE_GUARD',accepted_native_checkpoint=CP,normal_published_revision=REV,previous_public_main=BASE,previous_mathematical_sources_byte_identical=1026,whole_original_modules=5,original_pure_support_modules=3,complete_original_support_declarations=3,complete_blueprint_chapters=5,complete_original_blueprint_proofs=12,complete_blueprint_labelled_nodes=13,labelled_definition_without_proof=1,every_labelled_nondefinition_has_complete_proof=True,local_blueprint_bindings=22,new_module_targets=8,root_changes_only_recorded_imports=3,private_ledger_required=False,original_type_proof_text_changes=0,frozen_tool_profiles_unchanged=True)
whole_sources=load('provenance.json');supports=load('new-support-provenance.json');contexts=load('original-support-contexts.json')
assert len(whole_sources)==5 and len(supports)==len(contexts)==3
assert sum(len(r['administrative_elaboration_contexts']) for r in whole_sources)==2
assert load('owned-administrative-contexts.json')=={r['destination_module']:r['administrative_elaboration_contexts'] for r in whole_sources if r['administrative_elaboration_contexts']}
for changes in load('owned-administrative-contexts.json').values():
 for c in changes:
  assert all(line.startswith('import ') for line in c['before'].splitlines()+c['after'].splitlines())
for r in whole_sources+supports:
 path=r.get('destination_path',r['destination_module'].replace('.','/')+'.lean');assert digest(ROOT/path)==r['destination_sha256']
for r in contexts:assert r['omitted_original_proof_tokens']==0 and digest(ROOT/r['destination_path'])==r['destination_sha256']
for r in load('frozen-tool-profiles.json'):assert digest(ROOT/r['path'])==r['sha256']
proofs=0;actual=0
for filename,n,p in [('whole-module-full-expression-comparison.json',92,74),('fragment-full-expression-comparison.json',3,3)]:
 r=load(filename)
 expect(r,status='EXACT_ALL_FULL_EXPR_DAG_MATCH',missing=[],native_extras=[],approved_native_extras=[],unapproved_native_extras=[],differences=[],fallbacks=0,auxiliaries_skipped=0,proof_numbers_erased=0,binder_names_erased=0,defeq_or_alpha_comparison=False,metadata_preserved_in_full=True)
 assert r['old']['all_actual_constants']==r['native']['all_actual_constants']==n
 assert sum(v['theorems'] for v in r['module_counts'].values())==p
 for v in r['module_counts'].values():assert v['constants']==v['types_exact']==v['values_exact'] and v['theorems']==v['theorem_proofs_exact']
 assert r['comparator']['sha256']==digest(ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py')
 actual+=n;proofs+=p
assert (actual,proofs)==(95,77)
selection=load('fragment-all-public-root-selection.json')
expect(selection,status='PASS_ALL_ACTUAL_PUBLIC_SUPPORT_ROOTS_RETAINED_AND_ORIGINAL_PARENT_ROWS_SELECTED_VERBATIM',original_parent_actual_roots=23,public_actual_roots=3,selected_original_roots=3,outside_selected_original_parent_roots=20,public_roots_filtered=0,selected_original_rows_rewritten=0)
captures={r['path']:r for r in load('recorded-full-expression-captures.json')}
assert set(captures)=={'native-full-expressions.jsonl','public-full-expressions.jsonl','fragment-native-parent-all-actual-full-expressions.jsonl','fragment-native-full-expressions.jsonl','fragment-public-full-expressions.jsonl'}
for r in captures.values():assert digest(A/r['gzip_path'])==r['gzip_sha256'] and (A/r['gzip_path']).stat().st_size==r['gzip_bytes']
for filename in ['whole-module-full-expression-comparison.json','fragment-full-expression-comparison.json']:
 for side in ['old','native']:
  r=load(filename)[side];assert captures[Path(r['path']).name]['sha256']==r['sha256']
assert selection['original_parent_sha256']==captures['fragment-native-parent-all-actual-full-expressions.jsonl']['sha256']
assert 'PASS_ALL_95_RECORDED_ACTUAL_ROOTS_AND_77_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON' in (A/'recorded-full-expression-replay.log').read_text()
build=(A/'build-02-complete-original-base-congruence.log').read_text();assert 'Build completed successfully (5026 jobs).' in build and not re.search(r'(?im)^.*\b(?:warning|error):',build)
assert 'Unknown identifier `BlowupTowerSplitIso.IsTowerIso.congr_base`' in (A/'build-01-frozen-original-whole.log').read_text()
compiled=(A/'all-actual-roots-final.log').read_text()
for marker in ['ALL_LIBRARY_MODULES 1035; ALL_LIBRARY_ACTUAL_ROOTS 17169; NEW_MODULES 8; NEW_ACTUAL_ROOTS 95; EXACT_BINDINGS 22; MISSING 0; STANDARD_THREE_ONLY','SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4335; MISSING 0','ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5494; MISSING 0']:assert marker in compiled
for name,n in [('new-local-bindings.json',22),('complete-blueprint-local-bindings.json',4335),('all-document-local-bindings.json',5494)]:assert len(load(name))==len(set(load(name)))==n
peer=load('g3-original-support-and-context-review.json')
expect(peer,status='PASS_INDEPENDENT_ENTIRE_ORIGINAL_SUPPORT_CONTEXT_AND_WHOLE_SOURCE_FIDELITY_SCOPE_REVIEW',normal_published_revision=REV,accepted_native_checkpoint=CP,complete_original_support_declarations=3,complete_original_contexts=3,complete_blueprint_chapters=5,complete_blueprint_proofs=12,labelled_nodes=13,ordinary_definition_without_artificial_proof=1,whole_administrative_import_changes=2,whole_type_proof_changes=0,support_type_proof_token_changes=0,heavy_checks_repeated=False)
for r in peer['whole_modules']:
 own=next(v for v in whole_sources if v['destination_module']==r['module']);assert own['source_sha256']==r['source_sha256'] and own['destination_sha256']==r['destination_sha256']
for r in peer['original_supports']:
 own=next(v for v in supports if v['destination_module']==r['module']);assert own['source_parent_sha256']==r['parent_sha256'] and own['source_complete_declaration_sha256']==r['declaration_sha256'] and own['destination_sha256']==r['destination_sha256']
for name,h in peer['file_sha256'].items():assert digest(A/name)==h,name
for name,r in peer['observed_final_strict_gates'].items():assert digest(A/name)==r['sha256']
assert digest(ROOT/'README.md')==peer['readme_sha256'] and digest(A/'prepare_readme_update.py')==peer['readme_generator_sha256']
before=load('kernel-artifacts-before.json');after=load('kernel-artifacts-after.json');assert before==after
assert after['mathematical_modules_including_root']==after['kernel_data_parts']==1035
assert set(after['sources'])=={'Hironaka.lean'}|{str(p.relative_to(ROOT)) for p in (ROOT/'Hironaka').rglob('*.lean')}
for category in ['sources','compiled_kernel_data_parts','compiled_import_metadata_sha256']:
 for name,h in after[category].items():assert digest(ROOT/name)==h,(category,name)
reuse=validate_reuse(A,after)
expect(reuse,reused_preceding_modules=1026,fresh_new_modules=8,fresh_additional_changed_previous_kernel_modules=0,fresh_mathematical_modules=8,all_1026_previous_mathematical_sources_byte_identical=True)
kernel=load('incremental-kernel-replay.json')
expect(kernel,status='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY',new_modules=8,fresh_mathematical_modules=8,new_module_exact_inventory=True,import_root_replayed_with_installed_LeanChecker=True,full_sources_and_kernel_parts_unchanged=True,total_local_modules=1035,total_kernel_parts=1035,previous_nonroot_modules_reused_from_identical_verified_checkpoint=1026,lean_num_threads=1,fresh_full_library_replay_claimed=False)
assert 'REPLAYED_EXACT_IMPORT_ROOT Hironaka' in (A/'import-root-kernel-replay.log').read_text()
observed=[s.removeprefix('replaying ') for s in (A/'incremental-kernel-replay.log').read_text().splitlines() if s.startswith('replaying ')]
assert sorted(observed)==sorted(load('new-module-targets.json'))==sorted(load('kernel-modules.json'))
native_bp=load('accepted-native-blueprint-scope-validation.json')
expect(native_bp,status='PASS_ALL_338_NATIVE_CHAPTERS_LABELLED_STATEMENTS_PROOFS_AND_DEFINITIONS',normal_published_revision=REV,accepted_native_source_checkpoint=CP,chapters=338,labelled_nodes=1042,complete_nonempty_proof_environments=1040,labelled_definition_nodes=29,labelled_definitions_without_proof=2,every_labelled_nondefinition_has_complete_proof=True,labelled_nondefinitions=1013,definition_proofs_manufactured=0,private_ledger_required=False)
expect(load('blueprint-new-statement-proof-scope.json'),status='PASS_EVERY_LABELLED_NONDEFINITION_HAS_COMPLETE_PROOF',labelled_nodes=13,complete_proofs=12,definition_nodes=1,definition_without_proof=1)
bp=load('blueprint-validation.json')
expect(bp,status='PASS_COMPLETE_BLUEPRINT_LATEX_NO_ERRORS',native_accepted_checkpoint=CP,normal_published_revision=REV,complete_synchronized_chapters=415,complete_original_proofs=1593,distinct_local_bindings=4335,verified_upstream_only_bindings=241,explicit_historical_unresolved_bindings=2,distinct_synchronized_references=4578,new_chapters=5,new_complete_original_proofs=12,new_local_bindings=22,new_bindings_overlap_with_previous=0,new_labelled_statement_nodes=13,new_labelled_nondefinitions_with_complete_proofs=12,new_labelled_definitions_without_proof=1,new_definition_proofs_manufactured=0,all_document_chapters=500,all_document_complete_proof_environments=2064,all_document_distinct_local_binding_spellings=5494,all_inputs_exist_and_are_unique=True,all_495_preceding_document_input_sources_byte_identical=True,private_reference_derivatives_exported=False,pages=812,pdf_bytes=4082543,latex_errors=0,latex_warning_occurrences=704,reference_warning_occurrences=703,pdf_bookmark_warning_occurrences=6,missing_pdf_destination_warning_occurrences=72,math_environment_warning_occurrences=1,reference_warning_inventory_unchanged_from_predecessor=True,missing_pdf_destination_inventory_unchanged_from_predecessor=True,latex_passes=3,final_cross_references_stable=True,input_sources_unchanged_during_render=True)
assert digest(A/bp['pdf_path'])==bp['pdf_sha256'] and digest(A/bp['input_source_digests_file'])==bp['input_source_digests_sha256']
inputs=load(bp['input_source_digests_file']);assert len(inputs)==501
for name,h in inputs.items():assert digest(ROOT/name)==h
assert len(load('master-documentation-contexts.json'))==1
legacy=A.parent/'analytic-coefficient-dictionary-and-chosen-overlaps-20261015'
for name in ['all-actual-raw-structural-comparison-final.json','final-validation.json']:
 path=legacy/name;assert subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+str(path.relative_to(ROOT))])==path.read_bytes()
assert json.loads((legacy/'all-actual-raw-structural-comparison-final.json').read_text())['status']=='BLOCKED_EXACT_DIFFERENCE'
expect(json.loads((legacy/'final-validation.json').read_text()),strict_complete_mathematical_types_and_values=1006,parser_frontend_definitions_separately_source_audited=3,parser_bodies_structural_equality_claimed=False,raw_all_actual_structural_status='BLOCKED_EXACT_DIFFERENCE')
readme=(ROOT/'README.md').read_text();assert readme==(A/'README-next-checkpoint.md.txt').read_text()
for phrase in ['**Three of the nine original gaps are closed: G5, G6 and G7.**','**Six broader gaps remain open:**',REV,'338-module','old canonical prefix and one actual admissible whole cut','closes the prepared all-bound/all-relative-dimension case','single global intermediate blowup schedule','BLOCKED_EXACT_DIFFERENCE','equality of those three bodies remains unclaimed']:assert phrase in readme,phrase
for path in [ROOT/'README.md',A/'verification.md']:
 for target in re.findall(r'\]\(([^)]+)\)',path.read_text()):
  if target.startswith('#') or re.match(r'\w+:',target):continue
  dest=path.parent/unquote(target.split('#',1)[0]);assert dest.exists() or dest==A/'final-validation.json',(path,target)
evidence=[p for p in sorted(A.iterdir()) if p.is_file() and p.name not in ['final-validation.json','final-validation.log'] and not p.name.endswith('.jsonl')]
report={'status':'PASS_ALL_PUBLICATION_GATES_FIXED_338_INCREMENT','normal_published_native_revision':REV,'accepted_native_source_checkpoint':CP,'native_project_tree':'2c4179b89bf8760d5073936aaf997c4e4e3772bd','previous_public_main':BASE,'accepted_native_continuation_modules':338,'later_native_checkpoints_included':False,'mathematical_modules':1034,'all_local_modules_including_root':1035,'all_actual_compiled_roots_standard_three_only':17169,'new_whole_modules':5,'new_support_modules':3,'new_actual_compiled_roots':95,'strict_complete_types_and_values':95,'strict_complete_theorem_proofs':77,'all_new_actual_private_and_generated_roots_strictly_compared':True,'new_parser_frontend_structural_differences':0,'new_whole_source_import_adjustments':2,'new_whole_instance_context_adjustments':0,'original_type_proof_text_changes':0,'full_build_jobs':5026,'full_build_warnings':0,'source_scope':source,'frozen_kernel_coverage':kernel,'accepted_native_blueprint_statement_scope':native_bp,'blueprint_source_and_pdf_scope':bp,'all_document_compiled_exact_local_bindings':5494,'independent_entire_source_and_scope_review':'g3-original-support-and-context-review.json','previous_1026_mathematical_sources_byte_identical':True,'previous_1026_complete_kernel_artifacts_byte_identical':True,'legacy_parser_disclosure':{'strict_math_roots':1006,'separately_source_audited_frontend_definitions':3,'raw_all_1009_structural_status':'BLOCKED_EXACT_DIFFERENCE','three_frontend_bodies_equality_claimed':False},'closed_original_gaps':['G5','G6','G7'],'general_original_gaps_still_open':['G1','G2','G3','G4','G8','G9'],'prepared_all_source_bound_all_relative_dimension_case_complete_with_old_CAN_and_one_whole_cut':True,'full_hironaka_complete':False,'fresh_full_library_kernel_replay_claimed':False,'captured_full_expression_comparison_reproduced_from_lossless_gzip':True,'initial_failed_missing_original_prerequisite_attempt_retained':True,'historical_evidence_preserved':True,'current_artifact_sha256':{p.name:digest(p) for p in evidence},'pdf_sha256':digest(A/bp['pdf_path']),'readme_sha256':digest(ROOT/'README.md'),'final_validation_method':'Read-only current source/kernel/import-metadata/input/capture/receipt guards; separate Lean, complete-expression and installed kernel gates are not inferred or rerun.'}
(A/'final-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if not isinstance(v,(dict,list))}))
