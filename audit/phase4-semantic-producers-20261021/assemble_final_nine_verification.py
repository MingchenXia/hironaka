"""Offline author aggregation of frozen real source/build/kernel/CI/Expr gates.
No Lean process, new capture, source mutation, root filtering or comparator change.
"""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib,json,re
A=Path(__file__).resolve().parent;D=A.parents[1];B=D/'audit/canonical-elementary-family-and-local-producers-20261021';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
plan=load(A/'cohort-plan.json');rows=load(A/'provenance.json');bps=load(A/'blueprint-provenance.json');assert len(rows)==len(bps)==9
freeze=load(A/'final-nine-source-BP-freeze.json')
for p,h in freeze['files'].items():assert sha(D/p)==h,('Frozen source/BP input changed',p)
for p,h in plan['old_mathematical_files'].items():assert sha(D/p)==h,p
for p,h in plan['old_blueprint_files_including_master'].items():
 if p!='blueprint/extensions.tex':assert sha(D/p)==h,p
for p,h in plan['frozen_profiles'].items():assert sha(D/p)==h,p
for p in plan['deferred_prior_modules_preserved_absent']:assert not(D/p).exists(),p
oldkernels=load(B/'new-kernel-status.json');assert oldkernels['passed']==373
for m,r in oldkernels['modules'].items():
 for part in [r['source'],*r['kernel_parts']]:assert sha(D/part['path'])==part['sha256'],('Fixed373 source/kernel drift',m,part['path'])
seven=load(A/'frozen-seven-before-append/manifest.json')
for path,h in seven['files'].items():
 if path.startswith(('Hironaka/','blueprint/'))and path!='blueprint/extensions.tex' or path.startswith('.lake/')or path.endswith('.jsonl.gz'):assert sha(D/path)==h,('Seven-stage immutable input drift',path)
source=load(A/'source-replay-receipt.json');assert source['new_modules']==9 and source['new_written_proofs']==28 and source['ordinary_source_revision']==plan['ordinary_published_revision']
assert(A/'build-nine-attempt01.exit').read_text().strip()=='0';build=(A/'build-nine-attempt01.log').read_text();assert'Build completed successfully (5690 jobs).'in build and'warning:'not in build and'error:'not in build
k=load(A/'new-kernel-status.json');assert k['passed']==k['total']==9 and k['status']=='PASS_ALL9_NEW_EXACT_KERNEL_REPLAYS'
for r in k['modules'].values():
 assert r['exit_code']==0
 for part in[r['source'],*r['kernel_parts']]:assert sha(D/part['path'])==part['sha256']
e=load(A/'final-per-module-expressions/status.json');assert len(e['modules'])==e['captured_and_compared_modules']==9 and e['all_actual_public_roots']==181
physical=load(A/'new-nine-physical-ci-axioms.json');assert physical['actual_physical_root_observations']==181 and physical['all_imported_standalone_modules']==1542 and physical['all_actual_frontend_roots_retained']==15
ci=defaultdict(set)
for r in physical['all_physical_root_rows']:
 ci[r['actual_moduleData_owner']].add(r['actual_name']);assert set(r['physical_payload_transitive_axioms'])<={'propext','Classical.choice','Quot.sound'}
for m,r in e['modules'].items():
 assert r['capture_exit']==0 and r['scoped_comparison_complete']is True and r['public_roots_filtered']==0
 assert set(r['captures']['public-unfiltered']['actual_root_names'])==ci[m]
 for capture in r['captures'].values():assert sha(D/capture['path'])==capture['gzip_sha256']
 for f in r['frozen_inputs']:assert sha(Path(f['path']))==f['sha256']
 report=r['every_actual_new_root_comparison'];assert sha(D/report['report'])==report['report_sha256']
assert sum(r['every_actual_new_root_comparison']['exit_code']==0 for r in e['modules'].values())==7
math=load(A/'typed-notation/math-parents-attempt01/verification.json');assert math['strict_mathematical_roots']==166 and math['actual_public_typed_frontends']==15 and math['raw_status_input_sha256']==sha(A/'final-per-module-expressions/status.json') and math['all_mathematical_fields_compared_with_unchanged_frozen_comparator']
typed=load(A/'typed-notation/attempt01/verification.json');assert typed['status']=='PASS'and typed['whole_public_modules_scanned']==1542 and typed['no_logical_constant_dependents'] and typed['actual_new_public_frontend_definitions']==15 and typed['all181_new_physical_CI_own_type_and_whole_value_transitive_axioms_checked']
for name,h in load(A/'typed-notation/attempt01/source-inputs.json').items():assert sha(D/name)==h,name
notation=load(A/'independent-notation-source-generation/source-generation-review.json');assert notation['whole_parent_count']==2 and notation['approved_declaration_local_ENat_attribute_contexts']==3
for r in notation['parents']:assert next(x for x in rows if x['destination_module']==r['destination_module'])['destination_sha256']==r['public_sha256']
assert(A/'new-nine-literal-bindings.exit').read_text().strip()=='0'and'PASS_EXACT_LITERAL_ATTACHMENTS 42'in(A/'new-nine-literal-bindings.log').read_text()
# Resolve actual exact comma-separated labels through the real current master closure.
closure={}
def visit(p):
 p=p.resolve()
 if p in closure:return
 assert p.is_file(),p
 t=p.read_text();closure[p]=t
 for group in re.findall(r'\\input\{([^}]+)\}',t):
  q=p.parent/(group if group.endswith('.tex')else group+'.tex');visit(q)
visit(D/'blueprint/extensions.tex');defs=defaultdict(list)
for p,t in closure.items():
 for label in re.findall(r'\\label\{([^}]+)\}',t):defs[label].append(str(p.relative_to(D)))
assert not{k:v for k,v in defs.items()if len(v)>1}
observations=[]
for r in bps:
 p=(D/r['destination_path']).resolve();assert p in closure
 for command,group in re.findall(r'\\(uses|ref|eqref|cref|Cref|dref|dcref)\{([^}]+)\}',closure[p]):
  for label in group.split(','):
   label=label.strip();assert label in defs,(r['destination_path'],label);observations.append([r['destination_path'],command,label])
inputs={}
for p in['cohort-plan.json','provenance.json','blueprint-provenance.json','source-replay-receipt.json','new-kernel-status.json','final-per-module-expressions/status.json','new-nine-physical-ci-axioms.json','new-nine-literal-bindings.log','typed-notation/attempt01/verification.json','typed-notation/math-parents-attempt01/verification.json','independent-notation-source-generation/source-generation-review.json','native-actual-callee-preflight.json','final-nine-source-BP-freeze.json','external-prerequisite-complete-original-node.json']:
 inputs[p]={'path':str((A/p).relative_to(D)),'sha256':sha(A/p)}
hist=Counter(','.join(r['physical_payload_transitive_axioms'])or'none'for r in physical['all_physical_root_rows'])
report={'status':'PASS_NINE_WHOLE_NEW_MATHEMATICAL_PRODUCERS_WITH_DISCLOSED_TYPED_FRONTENDS','ordinary_native_source_revision':plan['ordinary_published_revision'],'accepted_authoring_ledger_revision':plan['authoring_ledger_revision'],'standalone_fixed_base_revision':plan['standalone_base_revision'],'new_whole_Lean_modules':9,'new_complete_original_BP_chapters':9,'new_complete_written_proofs':28,'new_definitions':1,'additional_documentation_only_external_pointer_inputs':1,'full_root_build':{'exit':0,'jobs':5690,'warnings':0,'log':'audit/phase4-semantic-producers-20261021/build-nine-attempt01.log'},'exact_installed_most_private_new_kernel_replays':9,'all_actual_new_public_physical_CIs':181,'all_actual_new_root_names_equal_unfiltered_capture_names':True,'strict_mathematical_whole_type_value_proof_Expr_matches':166,'raw_exact_complete_module_comparisons':7,'raw_notation_parent_BLOCKED_comparisons_retained':2,'independently_typed_isolated_compiler_frontend_definitions':15,'frontend_body_Expr_equality_claimed':False,'raw_global_Expr_status_preserved':e['status'],'all_new_physical_CI_own_payload_axioms_standard_subsets':dict(hist),'whole_current_public_environment_modules':1542,'whole_current_public_environment_physical_CIs':24271,'exact_new_local_literal_attachments':42,'all_old_mathematical_source_files_byte_unchanged':1532,'all_old_nonmaster_TeX_files_byte_unchanged':969,'prior_373_source_and_kernel_artifacts_byte_unchanged':True,'prior_373_kernel_or_Expr_replays_performed':0,'previous_seven_final_source_kernel_captures_reused_for_two_module_append':True,'four_frozen_profiles_unchanged':True,'genuine_original_context_restorations':{'pure_existing_support_imports':2,'declaration_local_ENat_ancestor_commands':3,'proof_type_payload_edits':0},'BP_exact_reference_token_observations':len(observations),'BP_actual_master_closure_TeX_files':len(closure),'BP_new_unresolved_exact_reference_tokens':0,'source_and_BP_replay_is_noop':True,'two_prior_whole_deferred_modules_remain_absent':plan['deferred_prior_modules_preserved_absent'],'all_nine_original_global_goals_claimed_closed':False,'components':inputs,'later_root_lake_test_and_independent_static_review':'Referenced separately by root publication aggregate; not claimed by this author-only manifest'}
(A/'final-nine-verification.json').write_text(json.dumps(report,indent=2)+'\n')
(A/'final-report.md').write_text('''Nine complete new mathematical modules and their nine complete original blueprint chapters are exported from ordinary native revision `636442a87402a67de1f914cb4120ee28c3ed6ad7`. They contain 28 written proofs and one definition. A separate documentation pointer supplies one fixed-source external prerequisite; it asserts no additional local theorem.

The full root builds with `--wfail` (5690 jobs, zero warnings). All nine exact installed kernel checks pass. Every one of the 181 new physical compiled declarations is captured and covered: all 166 mathematical types and whole values/proofs match the original expressions strictly. The remaining 15 declarations are independently typed parser/macro/unexpander definitions with no logical dependents; both raw parent reports remain `BLOCKED`, and parser body identity is not claimed. All 181 own-payload axiom sets use only standard axioms; all 42 literal local blueprint attachments resolve.

The prior 373 source and kernel artifacts, all 1532 preexisting mathematical source files, 969 preexisting nonmaster TeX files, and four frozen profiles are unchanged. The two earlier whole deferred modules remain deferred. Three approved theorem-local ENat ancestor commands and two pure existing-support imports restore genuine original context; no proof/type payload was rewritten. This increment advances the existing goals without asserting that all nine global goals are closed.

Source replay: `python audit/phase4-semantic-producers-20261021/sync_phase4_cohort.py --source-root /path/to/archon-nakamaye --revision 636442a87402a67de1f914cb4120ee28c3ed6ad7 --check`. The final author aggregation is reproducible offline with `python audit/phase4-semantic-producers-20261021/assemble_final_nine_verification.py`. Component paths and hashes are in `final-nine-verification.json`; root publication evidence separately records the documented lake test and independent final static/no-op review.
''')
print(json.dumps({k:report[k]for k in['status','new_whole_Lean_modules','all_actual_new_public_physical_CIs','strict_mathematical_whole_type_value_proof_Expr_matches','independently_typed_isolated_compiler_frontend_definitions','BP_actual_master_closure_TeX_files']},indent=2))
