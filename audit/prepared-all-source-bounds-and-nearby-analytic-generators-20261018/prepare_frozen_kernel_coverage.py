"""Classify every actual local module for fresh replay or byte-identical prior coverage."""
from pathlib import Path
import hashlib,json,subprocess,sys
from validate_previous_reuse import module_parts,validate_reuse
here=Path(__file__).resolve().parent;root=here.parents[1];previous=here.parent/'analytic-strict-generators-and-coupled-global-endpoint-20261018'
subprocess.run([sys.executable,str(here/'snapshot_kernel_artifacts.py'),str(here/'kernel-artifacts-before.json')],cwd=root,check=True)
before=json.loads((here/'kernel-artifacts-before.json').read_text());raw=(previous/'kernel-artifacts-after.json').read_bytes();old=json.loads(raw)
oldmods={s.removesuffix('.lean').replace('/','.') for s in old['sources'] if s!='Hironaka.lean'}
newmods=set(json.loads((here/'new-module-targets.json').read_text()));reuse=[];changed=[]
for m in sorted(oldmods):
 source=m.replace('.','/')+'.lean';assert before['sources'][source]==old['sources'][source]
 if module_parts(before['compiled_kernel_data_parts'],m)==module_parts(old['compiled_kernel_data_parts'],m):reuse.append(m)
 else:changed.append(m)
targets=sorted(newmods|set(changed));(here/'kernel-modules.json').write_text(json.dumps(targets,indent=2)+'\n')
guard={'status':'PASS_PINNED_PREDECESSOR_COMPLETE_SOURCE_AND_KERNEL_PART_REUSE_GUARD','previous_public_main':'2342eead0cdd7bba08acb2456e275a916bab94cf','previous_snapshot_sha256':hashlib.sha256(raw).hexdigest(),'previous_kernel_receipt_sha256':hashlib.sha256((previous/'incremental-kernel-replay.json').read_bytes()).hexdigest(),'reused_exact_module_inventory':reuse,'additional_changed_previous_kernel_modules_fresh_replay':changed,'fresh_exact_mathematical_module_inventory':targets,'previous_source_repair_count':0,'root_requires_separate_fresh_replay':True,'fresh_replay_claimed_passed_here':False}
(here/'previous-frozen-kernel-data-reuse.json').write_text(json.dumps(guard,indent=2)+'\n');print(json.dumps(validate_reuse(here,before)))
