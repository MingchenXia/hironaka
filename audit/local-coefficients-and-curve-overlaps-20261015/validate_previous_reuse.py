"""Bind the reused kernel-coverage claim to its pinned verified predecessor."""
from pathlib import Path
import hashlib,json

def validate_reuse(here, before):
    guard=json.loads((here/'previous-frozen-kernel-data-reuse.json').read_text())
    previous=here.parent/'retained-recipes-and-reduced-division-20261015'
    raw=(previous/'kernel-artifacts-after.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==guard['previous_snapshot_sha256']
    assert guard['status']=='PASS_ALL_817_PREVIOUS_NONROOT_SOURCES_AND_KERNEL_PARTS_BYTE_IDENTICAL'
    receipt=json.loads((previous/'incremental-kernel-replay.json').read_text())
    assert receipt['status']=='PASS_ALL_NEW_MODULES_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
    old=json.loads(raw);assert receipt['total_local_modules']==old['mathematical_modules_including_root']
    modules=0
    for source,digest in old['sources'].items():
        if source=='Hironaka.lean':continue
        assert before['sources'][source]==digest,source
        modules+=1
    for part,digest in old['compiled_kernel_data_parts'].items():
        if part.startswith('.lake/build/lib/lean/Hironaka.olean'):continue
        assert before['compiled_kernel_data_parts'][part]==digest,part
    assert modules==guard['reused_nonroot_modules']==817
    return modules

if __name__=='__main__':
    here=Path(__file__).resolve().parent
    count=validate_reuse(here,json.loads((here/'kernel-artifacts-before.json').read_text()))
    print('PASS_PINNED_PREDECESSOR_REUSE_'+str(count)+'_NONROOT_MODULES')
