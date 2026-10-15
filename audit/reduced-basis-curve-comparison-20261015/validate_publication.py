"""Validate exact source, compiled expression, kernel and documentation evidence."""
from pathlib import Path
import json,hashlib,re,subprocess
p=Path(__file__).resolve().parent
root=p.parents[1]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
read=lambda f:json.loads((p/f).read_text())
whole=read('whole-module-full-expression-comparison-final-08.json')
frag=read('fragment-full-expression-comparison.json')
kernel=read('incremental-kernel-replay.json')
replay=read('published-source-replay.json')
bp=read('blueprint-validation.json')
assert whole['status']==frag['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
assert whole['old']['all_actual_constants']==whole['native']['all_actual_constants']==1651
assert frag['old']['all_actual_constants']==frag['native']['all_actual_constants']==5
for report in [whole,frag]:
    assert not report['differences'] and not report['missing'] and not report['native_extras']
    assert report['fallbacks']==0 and report['auxiliaries_skipped']==0
    assert report['proof_numbers_erased']==0 and report['binder_names_erased']==0
    assert not report['defeq_or_alpha_comparison'] and report['metadata_preserved_in_full']
assert kernel['status']=='PASS_ALL_NEW_MODULES_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
assert kernel['new_modules']==52 and kernel['total_local_modules']==796
assert not kernel['fresh_full_library_replay_claimed']
build=(p/'build-08-original-import-order.log').read_text()
assert 'Build completed successfully (4766 jobs).' in build and 'warning:' not in build.lower()
assert 'ALL_LIBRARY_MODULES 796; ALL_LIBRARY_ACTUAL_ROOTS 14022; NEW_MODULES 52; NEW_ACTUAL_ROOTS 1656; EXACT_BINDINGS 810; MISSING 0; STANDARD_THREE_ONLY' in (p/'all-actual-roots-final-08.log').read_text()
assert 'PASS_ALL_1656_RECORDED_ACTUAL_ROOTS_FULL_STRUCTURAL_COMPARISON' in (p/'recorded-full-expression-replay.log').read_text()
assert replay['status']=='PASS_EXACT_PUBLISHED_SOURCE_REPLAY_AND_OLD_SOURCE_GUARD'
assert replay['old_mathematical_modules_byte_identical']==743 and replay['complete_new_modules']==49
before=read('kernel-artifacts-before.json');after=read('kernel-artifacts-after.json')
assert before==after
for group in ['sources','compiled_kernel_data_parts']:
    for file,digest in after[group].items():assert sha(root/file)==digest,file
frozen={
 'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean':'49aba8c3a923533a210946026b6ac67556c82e79d0c603b10c5b15994cf055ab',
 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py':'28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063',
 'scripts/sync_upstream_subgoal.py':'e49a4f622fd27d452953bff970cc429dc0077d98e084b078bdddc01d77b229fe'}
for file,digest in frozen.items():assert sha(root/file)==digest,file
for file in ['scripts/upstream_namespace_map.py','scripts/upstream_elaboration_contexts.json']:
    original=subprocess.check_output(['git','show','b7dc36db8a811e71c6b80938a5c89e75ee9e14f2:'+file],cwd=root)
    assert (root/file).read_bytes()==original,file
for review in ['scoped-owner-peer-review.json','recorded-expression-wrapper-peer-review.json']:
    data=read(review)
    assert data['status'].startswith('PASS'),review
proofs=sum(v['theorems'] for v in whole['module_counts'].values())+sum(v['theorems'] for v in frag['module_counts'].values())
assert proofs==1386,proofs
s=(root/'README.md').read_text()
assert '**Three of the nine original gaps are closed: G5, G6 and G7.**' in s
local_links=[target.split('#')[0] for target in re.findall(r'\]\(([^)]+)\)',s)
             if not target.startswith(('https://','http://','#'))]
pending=str((p/'final-validation.json').relative_to(root))
assert all((root/file).exists() or file==pending for file in local_links)
r={'status':'PASS_ALL_PUBLICATION_GATES','source_checkpoint':'7726587fed8e52e34c41d069ddd5ed7eee83e33a',
 'published_upstream_revision':'d7bd3eabbaa5853f5062bd38e5f358c2d462c1a4','whole_new_modules':49,
 'new_support_modules':3,'all_actual_new_roots':1656,'new_complete_types_and_values_exact':1656,
 'new_complete_theorem_proofs_exact':proofs,'old_mathematical_modules_byte_identical':743,
 'all_local_modules_including_root':796,'mathematical_modules':795,'all_actual_library_roots':14022,
 'standard_three_axioms_only':True,'build_jobs':4766,'build_warnings':0,'kernel_coverage':kernel,
 'blueprint':bp,'no_alpha_defeq_numeric_or_metadata_erasure':True,
 'frozen_v2_serializer_and_comparator_unchanged':True,'new_scoped_actual_owner_roots':5,
 'all_new_compiled_roots_included':True,'private_reference_derivatives_exported':False,
 'gaps_closed':['G5','G6','G7'],'broader_gaps_remaining':['G1','G2','G3','G4','G8','G9'],
 'full_hironaka_complete':False,'readme_local_links_checked':True}
(p/'final-validation.json').write_text(json.dumps(r,indent=2)+'\n')
assert all((root/file).exists() for file in local_links)
print(json.dumps({k:r[k] for k in ['status','mathematical_modules','all_local_modules_including_root',
 'all_actual_library_roots','all_actual_new_roots','new_complete_theorem_proofs_exact',
 'build_jobs','build_warnings','full_hironaka_complete']}))
