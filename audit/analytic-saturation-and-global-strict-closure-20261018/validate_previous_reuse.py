"""Validate every reused old source and complete kernel artifact against public PR8."""
from pathlib import Path
import hashlib,json,subprocess
BASE='9af2f7c9484b15a45282d098396261a682fb3f93'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def module_parts(parts,module):
 prefix='.lake/build/lib/lean/'+module.replace('.','/')+'.olean'
 return {k:v for k,v in parts.items() if k==prefix or k in (prefix+'.server',prefix+'.private')}
def validate_reuse(here,before):
 root=here.parents[1];previous=here.parent/'analytic-completion-and-global-curve-atlas-20261018'
 guard=json.loads((here/'previous-frozen-kernel-data-reuse.json').read_text())
 oldraw=(previous/'kernel-artifacts-after.json').read_bytes();receiptraw=(previous/'incremental-kernel-replay.json').read_bytes()
 for n,raw in [('kernel-artifacts-after.json',oldraw),('incremental-kernel-replay.json',receiptraw)]:
  path=str((previous/n).relative_to(root));assert subprocess.check_output(['git','-C',str(root),'show',BASE+':'+path])==raw
 assert sha(oldraw)==guard['previous_snapshot_sha256'] and sha(receiptraw)==guard['previous_kernel_receipt_sha256']
 old=json.loads(oldraw);receipt=json.loads(receiptraw)
 assert receipt['status']=='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
 assert old['mathematical_modules_including_root']==receipt['total_local_modules']==1003
 paths={s.removesuffix('.lean').replace('/','.') : s for s in before['sources'] if s!='Hironaka.lean'}
 oldmods={s.removesuffix('.lean').replace('/','.') for s in old['sources'] if s!='Hironaka.lean'}
 assert len(oldmods)==1002 and len(paths)==1015
 fresh=set(json.loads((here/'new-module-targets.json').read_text()));assert len(fresh)==13 and fresh==set(paths)-oldmods
 reuse=[];changed=[]
 for m in sorted(oldmods):
  path=paths[m];assert before['sources'][path]==old['sources'][path]
  assert sha((root/path).read_bytes())==old['sources'][path]
  prior=module_parts(old['compiled_kernel_data_parts'],m);current=module_parts(before['compiled_kernel_data_parts'],m)
  assert prior and current
  if prior==current:reuse.append(m)
  else:changed.append(m)
 targets=json.loads((here/'kernel-modules.json').read_text());expected=fresh|set(changed)
 assert len(targets)==len(set(targets)) and set(targets)==expected
 assert set(reuse)|expected==set(paths) and not set(reuse)&expected
 assert guard['reused_exact_module_inventory']==reuse
 assert guard['additional_changed_previous_kernel_modules_fresh_replay']==changed
 assert set(guard['fresh_exact_mathematical_module_inventory'])==expected
 assert guard['status']=='PASS_PINNED_PREDECESSOR_COMPLETE_SOURCE_AND_KERNEL_PART_REUSE_GUARD'
 return {'reused_preceding_modules':len(reuse),'fresh_new_modules':len(fresh),'fresh_additional_changed_previous_kernel_modules':len(changed),'fresh_mathematical_modules':len(expected),'all_1002_previous_mathematical_sources_byte_identical':True}
if __name__=='__main__':
 here=Path(__file__).resolve().parent;print(json.dumps(validate_reuse(here,json.loads((here/'kernel-artifacts-before.json').read_text()))))
