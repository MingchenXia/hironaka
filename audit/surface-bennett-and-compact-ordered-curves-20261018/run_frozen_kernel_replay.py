"""Replay all uncovered modules and exact import root with installed LeanChecker."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
from prepare_frozen_kernel_coverage import classify
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
strict=json.loads((A/'strict-all-final-comparison.json').read_text())
assert strict['status'].startswith('PASS_ALL_') and strict['status'].endswith('_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS')
review=json.loads((A/'independent-root-final-source-and-strict-review.json').read_text())
assert review['status'].startswith('PASS'),review['status']
start=time.monotonic()
def snapshot(name):
 subprocess.run([sys.executable,str(A/'snapshot_kernel_artifacts.py'),str(A/name)],cwd=ROOT,env=env,check=True,stdout=subprocess.DEVNULL)
snapshot('kernel-artifacts-before.json');before=json.loads((A/'kernel-artifacts-before.json').read_text());coverage=classify(before)
assert coverage==json.loads((A/'previous-frozen-kernel-data-reuse.json').read_text())
targets=json.loads((A/'kernel-modules.json').read_text());assert targets==coverage['fresh_mathematical_modules']
with (A/'incremental-kernel-replay.log').open('w') as stream:
 result=subprocess.run(['lake','env','leanchecker','-v',*targets],cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
assert result.returncode==0,('Installed kernel replay failed',result.returncode)
observed=[line.removeprefix('replaying ') for line in (A/'incremental-kernel-replay.log').read_text().splitlines() if line.startswith('replaying ')]
assert sorted(observed)==sorted(targets) and len(observed)==len(targets)
with (A/'import-root-kernel-replay.log').open('w') as stream:
 result=subprocess.run(['lake','env','lean',str(A/'ReplayImportRoot.lean')],cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
assert result.returncode==0 and 'REPLAYED_EXACT_IMPORT_ROOT Hironaka' in (A/'import-root-kernel-replay.log').read_text()
snapshot('kernel-artifacts-after.json');after=json.loads((A/'kernel-artifacts-after.json').read_text());assert before==after
assert len(coverage['reused_old_public_mathematical_modules'])==1106
assert 1106+len(targets)+1==before['mathematical_modules_including_root']==1141
receipt={'status':'PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY','fresh_mathematical_modules':len(targets),'fresh_import_root_replayed_with_installed_LeanChecker':True,'previous_1106_public_modules_exact_source_and_kernel_parts_reused':True,'added_math_modules_covered':34,'total_local_modules':1141,'total_kernel_parts':before['kernel_data_parts'],'full_sources_and_kernel_parts_unchanged':True,'compiled_import_metadata_unchanged':True,'fresh_replay_exact_inventory':True,'coverage_guard_sha256':hashlib.sha256((A/'previous-frozen-kernel-data-reuse.json').read_bytes()).hexdigest(),'all_coverage_pinned_to_normal_public_git_checkpoints':True,'elapsed_seconds':round(time.monotonic()-start,3),'lean_num_threads':1,'fresh_full_library_replay_claimed':False}
(A/'incremental-kernel-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
