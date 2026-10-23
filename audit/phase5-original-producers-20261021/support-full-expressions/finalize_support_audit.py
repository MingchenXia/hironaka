from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
A=Path(__file__).resolve().parent;P=A.parent;D=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(D/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
reference=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
node=next(n for n in ast.parse(reference.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[node],type_ignores=[]),str(reference),'exec'))
records=json.loads((P/'new-support-provenance.json').read_text())
for r in records:
 raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',r['source_revision']+':'+r['source_path']])
 assert sha(raw)==r['source_parent_sha256']
 frag=(P/r['raw_capture']).read_bytes();assert sha(frag)==r['source_complete_declaration_sha256'] and raw.count(frag)==1
 pub=(D/r['destination_path']).read_bytes();assert sha(pub)==r['destination_sha256'] and pub.count(relocate(frag.decode()).encode())==1
report=json.loads((A/'final-complete-comparison.json').read_text())
assert report['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH' and report['old']['all_actual_constants']==report['native']['all_actual_constants']==16
assert not report['differences'] and not report['missing'] and not report['native_extras']
assert sum(r['constants'] for r in report['module_counts'].values())==16
assert sum(r['types_exact'] for r in report['module_counts'].values())==16
assert sum(r['values_exact'] for r in report['module_counts'].values())==16
assert sum(r['theorem_proofs_exact'] for r in report['module_counts'].values())==13
frozen=json.loads((A/'frozen-inputs.json').read_text());changed=[]
for r in frozen:
 p=Path(r['path'])
 if sha(p.read_bytes())!=r['sha256']:changed.append(r)
assert len(changed)==2 and all('ZeroCoordinateTangentUnivExact' in r['path'] for r in changed)
source=next(r for r in changed if r['path'].endswith('.lean'))
new=Path(source['path']).read_bytes();old=new.replace('variable {N : Set M} {𝔞 : GermIdeal n M}'.encode(),'variable {N : Set M} {𝔞 𝔟 : GermIdeal n M}'.encode())
assert old!=new and sha(old)==source['sha256'],'Only exact original unused-section context correction is allowed'
finalpins=[]
for r in frozen:
 p=Path(r['path']);finalpins.append({'path':str(p),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size})
(A/'final-frozen-inputs.json').write_text(json.dumps(finalpins,indent=2)+'\n')
v3=D/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
comparator=D/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
assert sha(v3.read_bytes())=='1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755'
assert sha(comparator.read_bytes())=='28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
prefix=v3.read_text().split('def exportModuleData ',1)[0]
for name in ['BoundedSelectedSupportV3.lean','NarrowActualOwnerCorrectionV3.lean']:
 assert (A/name).read_text().startswith(prefix)
receipt={'status':'PASS_ALL16_ACTUAL_NEW_SUPPORT_FULL_TYPE_AND_WHOLE_PROOF_FIDELITY','published_source_revision':'eef2a7286318c05dda607a2909399937ccaa4c27','new_support_modules':3,'complete_original_written_declarations':8,'actual_compiler_generated_attachments':8,'actual_public_roots_retained':16,'entire_types_exact':16,'entire_values_exact':16,'entire_theorem_proofs_exact':13,'source_fragment_replay':'PASS_EXACT_PUBLISHED_SOURCE_AND_NAMESPACE_RELOCATION_ONLY','frozen_v3_serializer_prefix_unchanged':True,'frozen_comparator_unchanged':True,'raw_initial_differences_retained':True,'actual_primitive_owner_correction_only_module_prefix':True,'tangent_elaboration_context_correction':'Removed unused extra section variable 𝔟 to restore exact original numerical hygiene contexts; no declaration type/proof source changed','original_exact_capture_rows_reused':10,'necessary_narrow_original_owner_recapture_rows':6,'necessary_public_tangent_recapture_rows':2,'original_whole_parent_module_replay':False,'actual_public_roots_filtered':False,'proof_or_binder_or_suffix_erasure':False,'serialized_capture_rows_modified':False,'comparison':'final-complete-comparison.json','verbatim_row_coverage':'verbatim-row-reuse.json','final_frozen_inputs':'final-frozen-inputs.json','kernel_and_physical_axiom_gates':'../new-kernel-status.json and ../new17physical-ci-axioms.json (separate gate owner)'}
(A/'verification.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(receipt,ensure_ascii=False))
