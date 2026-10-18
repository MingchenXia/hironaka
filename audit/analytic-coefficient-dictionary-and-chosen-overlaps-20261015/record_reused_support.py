"""Record frozen original declarations reused from unchanged public pure modules."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
here=Path(__file__).resolve().parent
dest=here.parents[1]
native=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
published=Path('/workspace/archon-nakamaye-publish')
revision='09dc511c4a14836a0287748d1a63f9f467f677d3'
sys.path.insert(0,str(dest/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
previous=dest/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
relocation=next(n for n in ast.parse(previous.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[relocation],type_ignores=[]),str(previous),'exec'))
sha=lambda b:hashlib.sha256(b).hexdigest()
configs=[
 ('BlowupStrictIdeal','Hironaka.Blowup.BlowupStrictIdealControlled','controlledTransform_vanishingIdeal'),
 ('BlowupTowerTransforms','Hironaka.Blowup.BlowupTowerRestrictLengthExact','length_restrict'),
 ('BlowupStrictIdeal','Hironaka.Blowup.BlowupStrictIdeal','idealPow_one_exceptionalDivisor'),
 ('ThinDimensionDrop','Hironaka.Analytic.ThinAnalyticDimensionBound','dimLE_pred_of_thin'),
 ('AnalyticSubsetOpens','Hironaka.Analytic.AnalyticSubsetOpenMaps','contMDiff_restrict'),
 ('StrictTransformSubvariety','Hironaka.Resolution.StrictTransformSubvariety','eq_closure_component'),
 ('FirstPass.ComplexAnalyticSubvarieties','Hironaka.Manifold.LocalHolomorphicOpenPartialExact',
   'LocalHolomorphicEquivAt.toOpenPartialHomeomorph'),
 ('AnalyticDimensionBasics','Hironaka.Analytic.GeometricPureDimension','IsPureDim'),
]
records=[]
for short,destination,suffix in configs:
    source='TranscendentalNakamaye.'+(short if short.startswith('FirstPass.') else 'Pending.'+short)
    source_path='TranscendentalNakamaye/'+source.replace('.','/')+'.lean'
    raw=subprocess.check_output(['git','-C',str(published),'show',revision+':'+source_path])
    assert raw==(native/(source.replace('.','/')+'.lean')).read_bytes()
    declarations=json.loads((native/'.lake/build/lib/lean'/(source.replace('.','/')+'.ilean')).read_text())['decls']
    found=[(n,r) for n,r in declarations.items() if n.endswith('.'+suffix)]
    assert len(found)==1,(source,suffix,found)
    name,r=found[0]
    sl,sc,el,ec=r[:4]
    lines=raw.decode().splitlines(keepends=True)
    fragment=lines[sl][sc:]+''.join(lines[sl+1:el])+lines[el][:ec] if sl!=el else lines[sl][sc:ec]
    destination_path=destination.replace('.','/')+'.lean'
    actual=(dest/destination_path).read_bytes()
    omitted_documentation=''
    retained_fragment=fragment
    if actual.count(relocate(fragment).encode())!=1:
        # The already-published length support retains the complete original
        # theorem/type/proof but omitted its leading documentation comment.
        # Record that historical presentation difference; do not edit the module.
        doc=re.match(r'^/--[\s\S]*?-/\n',fragment)
        assert doc is not None,(destination,suffix)
        omitted_documentation=doc[0]
        retained_fragment=fragment[len(omitted_documentation):]
    assert actual.count(relocate(retained_fragment).encode())==1,(destination,suffix)
    sidecar='reused-'+suffix+'-original-declaration.lean.txt'
    (here/sidecar).write_text(fragment)
    records.append({'published_native_revision':revision,'source_module':source,
      'source_path':source_path,'source_parent_sha256':sha(raw),
      'actual_original_declaration':name,'compiler_source_range':r[:4],
      'source_complete_declaration_file':sidecar,'source_complete_declaration_sha256':sha(fragment.encode()),
      'existing_public_omitted_original_documentation':omitted_documentation,
      'destination_module':destination,'destination_path':destination_path,
      'destination_sha256':sha(actual),'reason':'Reuse the existing complete pure public proof; do not emit a duplicate declaration.'})
(here/'reused-existing-support-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
print('Recorded',len(records),'original declarations reused from unchanged pure public modules')
