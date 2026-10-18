"""Reuse all old kernel parts only when exact pinned source and parts match."""
from pathlib import Path
import hashlib,json,subprocess,sys
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='964b18f9c1cf70c263f4d4351b826413450ddf74'
PREVIOUS='audit/zero-dimensional-centre-bennett-and-actual-global-histories-20261018'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def pinned(path):
 raw=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path]);assert(ROOT/path).read_bytes()==raw,('Pinned receipt changed',path)
 return json.loads(raw),sha(raw)
def parts(snapshot,module):
 stem='.lake/build/lib/lean/'+module.replace('.','/')+'.olean'
 return{k:v for k,v in snapshot['compiled_kernel_data_parts'].items()if k in [stem,stem+'.server',stem+'.private']}
def classify(snapshot):
 old,oldsha=pinned(PREVIOUS+'/kernel-artifacts-after.json');receipt,receiptsha=pinned(PREVIOUS+'/incremental-kernel-replay.json')
 assert receipt['status']=='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'and receipt['full_sources_and_kernel_parts_unchanged']
 oldmods={p[:-5].replace('/','.')for p in old['sources']if p!='Hironaka.lean'}
 current={p[:-5].replace('/','.')for p in snapshot['sources']if p!='Hironaka.lean'}
 new=set(json.loads((A/'all-new-public-module-targets.json').read_text()))
 assert len(oldmods)==1106 and len(current)==1140 and len(new)==34 and new==current-oldmods
 for m in oldmods:
  path=m.replace('.','/')+'.lean';assert snapshot['sources'][path]==old['sources'][path],('Old source changed',m)
  assert parts(snapshot,m)==parts(old,m)and parts(old,m),('Old complete kernel parts changed',m)
  meta='.lake/build/lib/lean/'+m.replace('.','/')+'.ilean'
  assert snapshot['compiled_import_metadata_sha256'][meta]==old['compiled_import_metadata_sha256'][meta],('Old compiler metadata changed',m)
  assert snapshot['actual_compiler_direct_imports'][m]==old['actual_compiler_direct_imports'][m]
 return{'status':'PASS_EXACT_PINNED_SOURCE_AND_COMPLETE_KERNEL_PART_COVERAGE','public_baseline':BASE,'baseline_snapshot_sha256':oldsha,'baseline_kernel_receipt_sha256':receiptsha,'all_1106_old_sources_and_complete_kernel_parts_byte_identical':True,'all_old_actual_compiler_import_metadata_byte_identical':True,'reused_old_public_mathematical_modules':sorted(oldmods),'fresh_mathematical_modules':sorted(new),'newly_added_math_modules':sorted(new),'import_root_fresh_replay_required':True,'fresh_replay_claimed_passed_here':False}
if __name__=='__main__':
 subprocess.run([sys.executable,str(A/'snapshot_kernel_artifacts.py'),str(A/'kernel-artifacts-before.json')],cwd=ROOT,check=True)
 coverage=classify(json.loads((A/'kernel-artifacts-before.json').read_text()));(A/'previous-frozen-kernel-data-reuse.json').write_text(json.dumps(coverage,indent=2)+'\n');(A/'kernel-modules.json').write_text(json.dumps(coverage['fresh_mathematical_modules'],indent=2)+'\n');print(json.dumps({k:len(v)if isinstance(v,list)else v for k,v in coverage.items()}))
