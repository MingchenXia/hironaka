"""Extract eight complete, unchanged published declarations; relocate namespaces only."""
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys
A=Path(__file__).resolve().parent
D=A.parents[1]
sys.path.insert(0,str(D/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
reference=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
node=next(x for x in ast.parse(reference.read_text()).body if isinstance(x,ast.FunctionDef) and x.name=='relocate')
exec(compile(ast.Module(body=[node],type_ignores=[]),str(reference),'exec'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rev='eef2a7286318c05dda607a2909399937ccaa4c27'
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
common='\nset_option autoImplicit false\nset_option linter.unusedSectionVars false\nopen Set Filter\nopen scoped Topology Manifold ContDiff\n\n'
specs=[
 ('DerivativeIdealAlong','ZeroCoordinateDerivativeUnivExact',['derivIdealAlong_univ','iterDerivIdealAlong_univ'],['Hironaka.MarkedIdeal.DerivativeIdealAlong','Hironaka.MarkedIdeal.DerivativeIdealCoherence','Hironaka.Support.TangentFieldUnivExact'],['HolomorphicIdealSheaves','DerivativeIdeal'],False),
 ('TangentDirectionAlong','ZeroCoordinateTangentUnivExact',['fieldDeriv_const','isTangentDirectionAlong_univ_iff'],['Hironaka.MarkedIdeal.TangentDirectionAlong','Hironaka.MarkedIdeal.MaximalContact','Hironaka.Support.ZeroCoordinateDerivativeUnivExact','Hironaka.Support.TangentFieldUnivExact'],['HolomorphicIdealSheaves','BlowupSequences','GermIdealOrder','DerivativeIdeal','DerivativeIdealAlong','GiraudAlong','BlowupFlatCoordinates','DerivativeIdealAlongCoherent','RelativePrincipalizationSpan'],False),
 ('HomogenizedIdealAlong','ZeroCoordinateHomogenizedUnivExact',['homogenizedIdealAlong_univ','derivMarkedAlong_eq_derivMarked','coeffMarkedAlong_eq_coeffMarked','isMaximalOrderAlong_univ_iff'],['Hironaka.MarkedIdeal.HomogenizedIdealAlong','Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact','Hironaka.Invariant.CompanionMaximalOrder','Hironaka.Support.ZeroCoordinateDerivativeUnivExact'],['HolomorphicIdealSheaves','BlowupSequences','GermIdealOrder','DerivativeIdeal','DerivativeIdealAlong','GiraudAlong','TangentDirectionAlong','IdealWeightPowers','MarkedIdeals','DerivativeIdealTower','CoefficientIdeal','HomogenizedGlueing','HomogenizedEquivalence','HomogenizedEtale','MarkedIdealBiholomorphism','GermIdealPullbackCalculus','HadamardBridge'],True)
]
captures=A/'new-support-original-captures';captures.mkdir(exist_ok=True)
records=[]
for parent,support,decls,imports,opens,explicit_u in specs:
 source_path=f'TranscendentalNakamaye/TranscendentalNakamaye/Pending/{parent}.lean'
 raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',rev+':'+source_path])
 (captures/(parent+'-complete-source.lean.txt')).write_bytes(raw)
 source=raw.decode();fragments=[];parts=[]
 for decl in decls:
  start=source.index('theorem '+decl+' ')
  rest=source[start:]
  # Only unindented source commands terminate a complete declaration.
  stop=re.search(r'\n(?=/--|/-!|(?:theorem|lemma|def|private|end|section|namespace|variable|open|attribute)\b|@\[)',rest)
  part=rest[:stop.start() if stop else len(rest)].rstrip()+'\n'
  assert part.startswith('theorem '+decl+' ') and part.count('\ntheorem ')==0
  assert source.count(part)==1
  capture=captures/(parent+'.'+decl+'.lean.txt');capture.write_text(part)
  fragments.append(relocate(part))
  parts.append({'source_revision':rev,'source_module':'TranscendentalNakamaye.Pending.'+parent,'source_path':source_path,'source_parent_sha256':sha(raw),'source_name':'TranscendentalNakamaye.Pending.'+parent+'.'+decl,'source_complete_declaration_sha256':sha(part.encode()),'raw_capture':str(capture.relative_to(A)),'destination_name':'Hironaka.'+parent+'.'+decl,'destination_module':'Hironaka.Support.'+support,'destination_path':'Hironaka/Support/'+support+'.lean','original_proof_tokens_changed':False})
 body=header+''.join('import '+m+'\n' for m in imports)+common
 if explicit_u:body+='universe u\n\n'
 body+='namespace Hironaka.'+parent+'\nopen '+' '.join('Hironaka.'+x for x in opens)+'\nnoncomputable section\n'
 body+='variable {n : ℕ} {M : '+('Type u' if explicit_u else 'Type*')+'} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]\n  [IsComplexManifold n M]\n'
 body+='variable {N : Set M} {𝔞'+(' 𝔟' if parent=='DerivativeIdealAlong' else '')+' : GermIdeal n M}\n\n'
 body+='\n'.join(fragments)+'\nend\nend Hironaka.'+parent+'\n'
 path=D/parts[0]['destination_path']
 if path.exists():assert path.read_text()==body,('Preexisting partial extraction differs',path)
 else:path.write_text(body)
 for part in parts:part['destination_sha256']=sha(path.read_bytes())
 records+=parts
(A/'new-support-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
rows=json.loads((A/'provenance.json').read_text());extras=json.loads((A/'additional-pure-support-imports.json').read_text())
row=next(r for r in rows if r['source_module'].endswith('.HironakaActualZeroCoordinateContactSeed'))
imports=['Hironaka.Support.ZeroCoordinateTangentUnivExact','Hironaka.Support.ZeroCoordinateHomogenizedUnivExact']
path=D/row['destination_path'];text=path.read_text()
if not row['additional_pure_support_imports']:
 first=re.search(r'^import ',text,re.M);text=text[:first.start()]+''.join('import '+x+'\n' for x in imports)+text[first.start():];path.write_text(text)
else:assert row['additional_pure_support_imports']==imports
row['additional_pure_support_imports']=imports;row['destination_sha256']=sha(path.read_bytes());extras[row['destination_module']]=imports
(A/'provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
(A/'additional-pure-support-imports.json').write_text(json.dumps(extras,indent=2)+'\n')
print(json.dumps({'complete_original_support_declarations':len(records),'new_support_modules':3,'proof_tokens_changed':False}))
