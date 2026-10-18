"""Cover every module using exact pinned prior kernel parts or fresh installed replay."""
from pathlib import Path
import hashlib,json,subprocess,sys
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='7f043d57b4052e6f8fc69c4abe4d762114a7666f'
REPAIR='4f034e0dab92eacb4375ab09a38515b63ccbd7cc'
PREVIOUS='audit/actual-differential-ideals-and-uniform-successor-stages-20261018'
REPAIRED='audit/actual-point-bennett-major-reproducibility-20261018'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def pinned(rev,path):
 raw=subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT)
 assert (ROOT/path).read_bytes()==raw,('prior receipt changed',path)
 return json.loads(raw),sha(raw)
def parts(snapshot,module):
 stem='.lake/build/lib/lean/'+module.replace('.','/')+'.olean'
 return {k:v for k,v in snapshot['compiled_kernel_data_parts'].items() if k==stem or k in [stem+'.server',stem+'.private']}
def classify(snapshot):
 old,oldsha=pinned(BASE,PREVIOUS+'/kernel-artifacts-after.json')
 oldreceipt,oldreceiptsha=pinned(BASE,PREVIOUS+'/incremental-kernel-replay.json')
 repair,repairsha=pinned(REPAIR,REPAIRED+'/kernel-artifacts-after.json')
 rr,rrsha=pinned(REPAIR,REPAIRED+'/incremental-kernel-replay.json')
 expected='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
 assert oldreceipt['status']==rr['status']==expected
 assert oldreceipt['full_sources_and_kernel_parts_unchanged'] and rr['full_sources_and_kernel_parts_unchanged']
 oldmods={p[:-5].replace('/','.') for p in old['sources'] if p!='Hironaka.lean'}
 repairmods={p[:-5].replace('/','.') for p in repair['sources'] if p!='Hironaka.lean'}
 current={p[:-5].replace('/','.') for p in snapshot['sources'] if p!='Hironaka.lean'}
 new=set(json.loads((A/'all-new-public-module-targets.json').read_text()))
 assert len(oldmods)==1042 and len(repairmods)==1053 and len(current)==1106
 assert new==current-oldmods and len(new)==64
 for m in oldmods:
  path=m.replace('.','/')+'.lean'
  assert snapshot['sources'][path]==old['sources'][path],('old source changed',m)
  assert parts(snapshot,m)==parts(old,m) and parts(old,m),('old kernel parts changed',m)
 prior_repair_reused=[];fresh=[];changed_repair=[]
 for m in sorted(new):
  path=m.replace('.','/')+'.lean'
  if m in repairmods and snapshot['sources'][path]==repair['sources'][path] and parts(snapshot,m)==parts(repair,m):
   assert parts(repair,m);prior_repair_reused.append(m)
  else:
   fresh.append(m)
   if m in repairmods:changed_repair.append(m)
 assert len(oldmods)+len(prior_repair_reused)+len(fresh)==1106
 return {'status':'PASS_EXACT_PINNED_SOURCE_AND_COMPLETE_KERNEL_PART_COVERAGE','public_baseline':BASE,'baseline_snapshot_sha256':oldsha,'baseline_kernel_receipt_sha256':oldreceiptsha,'previous_local_repair':REPAIR,'repair_snapshot_sha256':repairsha,'repair_kernel_receipt_sha256':rrsha,'old_1042_sources_and_all_kernel_parts_byte_identical':True,'reused_old_public_mathematical_modules':sorted(oldmods),'reused_repair_mathematical_modules':prior_repair_reused,'fresh_mathematical_modules':fresh,'changed_repair_mathematical_modules':changed_repair,'newly_added_math_modules':sorted(new),'import_root_fresh_replay_required':True,'fresh_replay_claimed_passed_here':False}
if __name__=='__main__':
 subprocess.run([sys.executable,str(A/'snapshot_kernel_artifacts.py'),str(A/'kernel-artifacts-before.json')],cwd=ROOT,check=True)
 result=classify(json.loads((A/'kernel-artifacts-before.json').read_text()))
 (A/'previous-frozen-kernel-data-reuse.json').write_text(json.dumps(result,indent=2)+'\n')
 (A/'kernel-modules.json').write_text(json.dumps(result['fresh_mathematical_modules'],indent=2)+'\n')
 print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in result.items()}))
