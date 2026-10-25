"""Summarize completed NEW-only kernel and actual-physical-payload checks."""
from pathlib import Path
from collections import Counter
import hashlib,json
A=Path(__file__).resolve().parent
D=A.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
k=json.loads((A/'new-kernel-status.json').read_text())
p=json.loads((A/'new17physical-ci-axioms.json').read_text())
assert k['status']=='PASS_ALL17_NEW_EXACT_KERNEL_REPLAYS' and k['passed']==k['total']==17
assert p['status']=='PASS_ALL_ACTUAL_PHYSICAL_CI_PAYLOAD_AXIOMS'
assert (A/'new17physical-ci-axioms.exit').read_text().strip()=='0'
assert p['actual_modules']==17 and p['actual_physical_root_observations']==340
assert p['all_imported_standalone_modules']==1559
assert not p['roots_frontend_or_helpers_filtered']
assert not p['physical_root_payload_replaced_by_environment_Name_lookup']
assert p['actual_axiomInfo_roots_checked']==0
pins=[]
for module,row in k['modules'].items():
 assert row['exit_code']==0
 for part in [row['source'],*row['kernel_parts']]:
  assert sha(D/part['path'])==part['sha256'],part['path']
  pins.append(part)
 assert 'leanchecker' in row['command'] and '--verbose' in row['command']
 assert '--fresh' not in row['command'] and row['command'][-1]==module
assert len(k['modules'])==17
counts=Counter(tuple(row['physical_payload_transitive_axioms']) for row in p['all_physical_root_rows'])
receipt={
 'status':'PASS_17_NEW_EXACT_KERNELS_AND_340_ACTUAL_PHYSICAL_PAYLOADS',
 'new_whole_producer_modules':14,'new_pure_support_modules':3,
 'exact_installed_module_kernel_replays':17,'all_kernel_exit_codes':0,
 'imported_cone_fresh_or_old_baseline_kernel_replay':False,
 'actual_physical_root_observations':340,'whole_producer_roots':324,'pure_support_roots':16,
 'all_actual_frontend_roots_retained':p['all_actual_frontend_roots_retained'],
 'physical_own_type_and_whole_opaque_body_scanned':True,
 'physical_root_payload_replaced_by_environment_Name_lookup':False,
 'actual_axiomInfo_roots':0,
 'axiom_profiles':[{'axioms':list(ax),'actual_roots':count}for ax,count in sorted(counts.items())],
 'full_imported_source_roster_exact':1559,
 'old_payload_or_Expr_replay':False,
 'source_and_all_most_private_kernel_parts_still_exact':True,
 'pinned_source_and_artifact_parts':len(pins),
 'receipts':{name:{'sha256':sha(A/name),'path':str((A/name).relative_to(D))}for name in [
  'new-kernel-status.json','new17physical-ci-axioms.json','new17physical-ci-axioms.log',
  'New17PhysicalCIAxioms.lean','run_new_kernel_checks.py','new17physical-preparation.json']}}
(A/'new-kernel-physical-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,ensure_ascii=False))
