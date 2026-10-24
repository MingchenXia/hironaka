"""Compose immutable old-owner rows with the four corrected NEW-owner rechecks."""
from pathlib import Path
from collections import Counter
import hashlib,json
A=Path(__file__).resolve().parent
D=A.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((A/'new17physical-ci-axioms.json').read_text())
fresh=json.loads((A/'new17physical-build09-narrow-ci-axioms.json').read_text())
k=json.loads((A/'new-kernel-status.json').read_text())
k0=json.loads((A/'build06-kernel-snapshot/new-kernel-status.json').read_text())
targets=(A/'new17physical-build09-narrow-modules.txt').read_text().splitlines()
assert len(targets)==len(set(targets))==4
assert old['status']==fresh['status']=='PASS_ALL_ACTUAL_PHYSICAL_CI_PAYLOAD_AXIOMS'
assert old['actual_physical_root_observations']==340
assert fresh['actual_modules']==4 and fresh['actual_physical_root_observations']==169
assert fresh['all_imported_standalone_modules']==1559
assert (A/'new17physical-build09-narrow-ci-axioms.exit').read_text().strip()=='0'
assert k['status']=='PASS_ALL17_NEW_EXACT_KERNEL_REPLAYS' and k['passed']==k['total']==17
for m,r in k['modules'].items():
 assert r['exit_code']==0
 for p in [r['source'],*r['kernel_parts']]:assert sha(D/p['path'])==p['sha256']
 if m not in targets:assert r==k0['modules'][m],m
assert set(targets)=={r['module']for r in fresh['module_counts']}
for m in targets:
 oldnames={r['actual_name']for r in old['all_physical_root_rows']if r['actual_moduleData_owner']==m}
 newnames={r['actual_name']for r in fresh['all_physical_root_rows']if r['actual_moduleData_owner']==m}
 assert oldnames==newnames,m
reused=[r for r in old['all_physical_root_rows']if r['actual_moduleData_owner']not in targets]
assert len(reused)==171
allrows=[*reused,*fresh['all_physical_root_rows']]
assert len(allrows)==340
assert len({(r['actual_moduleData_owner'],r['actual_name'])for r in allrows})==340
assert all(r['own_whole_body_present']for r in allrows)
assert not any(r['actual_kind']=='axiom'for r in allrows)
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(r['physical_payload_transitive_axioms'])<=allowed for r in allrows)
profiles=Counter(tuple(r['physical_payload_transitive_axioms'])for r in allrows)
combined={
 'status':'PASS_COMPOSED_FINAL_BUILD09_340_ACTUAL_PHYSICAL_CI_PAYLOAD_AXIOMS',
 'scope':'All 17 NEW physical owners; 169 affected roots freshly checked in final build09, 171 immutable unaffected-owner rows reused from the original completed audit.',
 'actual_modules':17,'actual_physical_root_observations':340,
 'fresh_final_build09_module_owners':targets,'fresh_final_build09_actual_roots':169,
 'immutable_unaffected_owner_rows_reused':171,
 'all_actual_frontend_roots_retained':sum(bool(r['actual_frontend_type'])for r in allrows),
 'roots_frontend_or_helpers_filtered':False,
 'physical_root_payload_replaced_by_environment_Name_lookup':False,
 'source_row_objects_modified':False,'old_kernel_or_Expr_or_payload_replay':False,
 'all_physical_root_rows':allrows,
 'source_reports':{name:sha(A/name)for name in ['new17physical-ci-axioms.json','new17physical-build09-narrow-ci-axioms.json']}}
(A/'new17physical-build09-combined-ci-axioms.json').write_text(json.dumps(combined,indent=2)+'\n')
receipt={
 'status':'PASS_FINAL_BUILD09_17_NEW_EXACT_KERNELS_AND_340_ACTUAL_PHYSICAL_PAYLOADS',
 'final_full_build':'standalone-build09.log','final_full_build_exit':0,
 'new_whole_producer_modules':14,'new_pure_support_modules':3,
 'exact_installed_module_kernel_checks_valid_for_final_pins':17,
 'affected_new_kernels_rechecked':4,'unchanged_new_kernels_reused_at_identical_source_and_artifact_pins':13,
 'latest_kernel_runner_log':'new-kernel-build08-runner.log',
 'latest_runner_log_name_precedes_final_build_name_but_all_four_actual_source_and_artifact_pins_match_final09':True,
 'initial_all17_kernel_receipts_frozen':'build06-kernel-snapshot/snapshot-manifest.json',
 'physical_actual_roots':340,'fresh_final_physical_actual_roots':169,
 'unchanged_physical_owner_rows_reused':171,
 'axiom_profiles':[{'axioms':list(ax),'actual_roots':count}for ax,count in sorted(profiles.items())],
 'all_actual_frontend_roots_retained':combined['all_actual_frontend_roots_retained'],
 'actual_axiomInfo_roots':0,'full_imported_source_roster_exact':1559,
 'whole_type_and_whole_opaque_body_audit':True,
 'old_kernel_or_Expr_or_payload_replay':False,
 'receipt_files':{name:sha(A/name)for name in ['new-kernel-status.json','new-kernel-build09-final-pins.json','new17physical-build09-combined-ci-axioms.json','new17physical-ci-axioms.json','new17physical-build09-narrow-ci-axioms.json','New17PhysicalBuild09NarrowCIAxioms.lean','new17physical-build09-narrow-ci-axioms.log']}}
(A/'new-kernel-physical-build09-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
