"""Replay all actual new modules and the changed import root, against frozen data."""
from pathlib import Path
import os,sys,json,time,subprocess,datetime
from validate_previous_reuse import validate_reuse
here=Path(__file__).resolve().parent;root=here.parents[1]
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
def snapshot(name):
 subprocess.run([sys.executable,str(here/'snapshot_kernel_artifacts.py'),str(here/name)],cwd=root,env=env,check=True,stdout=subprocess.DEVNULL)
start=time.monotonic();snapshot('kernel-artifacts-before.json');reused=validate_reuse(here,json.loads((here/'kernel-artifacts-before.json').read_text()));targets=json.loads((here/'kernel-modules.json').read_text())
with (here/'incremental-kernel-replay.log').open('w') as stream:
 result=subprocess.run(['lake','env','leanchecker','-v',*targets],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
if result.returncode:raise SystemExit(result.returncode)
with (here/'import-root-kernel-replay.log').open('w') as stream:
 root_result=subprocess.run(['lake','env','lean',str(here/'ReplayImportRoot.lean')],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
snapshot('kernel-artifacts-after.json');before=json.loads((here/'kernel-artifacts-before.json').read_text());after=json.loads((here/'kernel-artifacts-after.json').read_text());observed=[s.removeprefix('replaying ') for s in (here/'incremental-kernel-replay.log').read_text().splitlines() if s.startswith('replaying ')]
assert sorted(observed)==sorted(targets),'Unexpected or missing module in standard leanchecker replay'
assert before==after,'Sources or kernel artifacts changed during verification'
assert root_result.returncode==0 and 'REPLAYED_EXACT_IMPORT_ROOT Hironaka' in (here/'import-root-kernel-replay.log').read_text()
receipt={'status':'PASS_ALL_NEW_MODULES_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY','new_modules':len(targets),'new_module_exact_inventory':True,'import_root_replayed_with_installed_LeanChecker':True,'full_sources_and_kernel_parts_unchanged':True,'total_local_modules':before['mathematical_modules_including_root'],'total_kernel_parts':before['kernel_data_parts'],'previous_nonroot_modules_reused_from_identical_verified_checkpoint':reused,'previous_reuse_guard':'previous-frozen-kernel-data-reuse.json','elapsed_seconds':round(time.monotonic()-start,3),'lean_num_threads':1,'fresh_full_library_replay_claimed':False}
(here/'incremental-kernel-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
