"""Validate exact source, compiled expression, kernel and documentation evidence."""
from pathlib import Path
import json,hashlib,re,subprocess
p=Path(__file__).resolve().parent
root=p.parents[1]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
read=lambda f:json.loads((p/f).read_text())
whole=read('whole-module-full-expression-comparison.json')
frag=read('fragment-full-expression-comparison.json')
kernel=read('incremental-kernel-replay.json')
replay=read('published-source-replay.json')
bp=read('blueprint-validation.json')
assert whole['status']==frag['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
assert whole['old']['all_actual_constants']==whole['native']['all_actual_constants']==1082
assert frag['old']['all_actual_constants']==frag['native']['all_actual_constants']==6
for report in [whole,frag]:
    assert not report.get('differences', []) and not report['missing'] and not report['native_extras']
    assert report['fallbacks']==0 and report['auxiliaries_skipped']==0
    assert report['proof_numbers_erased']==0 and report['binder_names_erased']==0
    assert not report['defeq_or_alpha_comparison'] and report['metadata_preserved_in_full']
assert kernel['status']=='PASS_ALL_NEW_MODULES_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
assert kernel['new_modules']==70 and kernel['total_local_modules']==888
assert not kernel['fresh_full_library_replay_claimed']
build=(p/'build-06-original-equation-owner-and-local-instance.log').read_text()
assert 'Build completed successfully (4871 jobs).' in build and 'warning:' not in build.lower()
assert 'ALL_LIBRARY_MODULES 888; ALL_LIBRARY_ACTUAL_ROOTS 15562; NEW_MODULES 70; NEW_ACTUAL_ROOTS 1088; EXACT_BINDINGS 485; MISSING 0; STANDARD_THREE_ONLY' in (p/'all-actual-roots-final.log').read_text()
assert 'PASS_ALL_1088_RECORDED_ACTUAL_ROOTS_FULL_STRUCTURAL_COMPARISON' in (p/'recorded-full-expression-replay.log').read_text()
assert replay['status']=='PASS_EXACT_PUBLISHED_SOURCE_REPLAY_AND_OLD_SOURCE_GUARD'
assert replay['old_mathematical_modules_byte_identical']==817 and replay['complete_new_modules']==67
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
    original=subprocess.check_output(['git','show','a2644ad18502f8b7622ba535ba5e8c6e32156b9f:'+file],cwd=root)
    assert (root/file).read_bytes()==original,file
for review in ['publication-tools-peer-review.json','generated-equation-and-original-instance-peer-review.json']:
    data=read(review)
    assert data['status'].startswith('PASS'),review
proofs=sum(v['theorems'] for report in [whole,frag] for v in report['module_counts'].values())
assert proofs==877,proofs
s=(root/'README.md').read_text()
assert '**Three of the nine original gaps are closed: G5, G6 and G7.**' in s
local_links=[target.split('#')[0] for target in re.findall(r'\]\(([^)]+)\)',s)
             if not target.startswith(('https://','http://','#'))]
pending=str((p/'final-validation.json').relative_to(root))
assert all((root/file).exists() or file==pending for file in local_links)
r={'status':'PASS_ALL_PUBLICATION_GATES','source_checkpoint':'29018d27b93c641df6c26c761e3cb612a4aaa350',
 'published_upstream_revision':'7cfb7a24ea1c4d42a2d37faee1af3757637fc19b','whole_new_modules':67,
 'new_support_modules':3,'all_actual_new_roots':1088,'new_complete_types_and_values_exact':1088,
 'new_complete_theorem_proofs_exact':proofs,'old_mathematical_modules_byte_identical':817,
 'all_local_modules_including_root':888,'mathematical_modules':887,'all_actual_library_roots':15562,
 'standard_three_axioms_only':True,'build_jobs':4871,'build_warnings':0,'kernel_coverage':kernel,
 'blueprint':bp,'no_alpha_defeq_numeric_or_metadata_erasure':True,
 'frozen_v2_serializer_and_comparator_unchanged':True,'new_scoped_actual_owner_roots':0,
 'all_new_compiled_roots_included':True,'generated_equation_complete_type_and_proof_exact':True,'private_reference_derivatives_exported':False,
 'gaps_closed':['G5','G6','G7'],'broader_gaps_remaining':['G1','G2','G3','G4','G8','G9'],
 'full_hironaka_complete':False,'readme_local_links_checked':True}
(p/'final-validation.json').write_text(json.dumps(r,indent=2)+'\n')
assert all((root/file).exists() for file in local_links)
print(json.dumps({k:r[k] for k in ['status','mathematical_modules','all_local_modules_including_root',
 'all_actual_library_roots','all_actual_new_roots','new_complete_theorem_proofs_exact',
 'build_jobs','build_warnings','full_hironaka_complete']}))
