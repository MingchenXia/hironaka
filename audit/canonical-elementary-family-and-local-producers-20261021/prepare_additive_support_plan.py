"""Normalize independently prepared full-original support drafts; never install Lean/BP."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
A=Path(__file__).resolve().parent;DST=A.parents[1];sys.dont_write_bytecode=True
sys.path.insert(0,str(DST/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
F=DST/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(F.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');scope={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(F),'exec'),scope);relocate=scope['relocate']
sha=lambda b:hashlib.sha256(b).hexdigest();P=A/'additive40-prerequisite-integration-preparation';P.mkdir(exist_ok=True)
roster=json.loads(Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication/native8-recursive-callee-closure/ordinary-source-declarations-by-parent.json').read_text());parents={r['actual_native_parent'].rsplit('.',1)[-1]:r for r in roster}
# Each handoff contains separately checked whole original chunks and a complete balanced draft.
configs=[('MarkedIdealOperationsTransform','canonical-additive-marked-operations','proposed-plan-row.json','MarkedIdealOperationsMonotoneControlledOriginalExact.lean','row'),('RestrictEmptyTower','root-additive-empty-tower','proposed-plan-row.json','RestrictEmptyTowerCentresOverOriginalExact.lean','row'),('CoefficientRestrictionTower','setup-additive-coefficient-tower','extraction-audit.json','CoefficientRestrictionTowerIffOriginalExact.lean','row'),('NormalDerivativeChart','setup-additive-normal-derivative','extraction-audit.json','NormalDerivativeChartIdealOriginalExact.lean','row'),('OrderMultiplicativity','setup-additive-order-powers','extraction-audit.json','OrderMultiplicativityCosupportOriginalExact.lean','row'),('MemberInterTowerAlong','tangent-additive-member-inter','integration-sidecar.json','MemberInterTowerAlongOriginalExact.lean','tangent'),('DerivativeIdealTower','tangent-additive-derivative-tower','integration-sidecar.json','DerivativeIdealTowerOriginalExact.lean','tangent'),('CoefficientIdealRestriction','principal-additive-coefficient-restriction/complete-five','plan.json','CoefficientRestrictionSupportOriginalExact.lean','principal'),('DropMembers','defect-additive-drop-members','extraction-audit.json','DropMembersContainingCentresOriginalExact.lean','drop'),('CoefficientIdeal','defect-additive-coefficient-ideal','extraction-audit.json','CoefficientIdealTowerOperationsOriginalExact.lean','coefficient')]
plans=[]
for stem,folder,contract,draftname,kind in configs:
 folder=A/'support-prep'/folder;c=folder/contract;d=json.loads(c.read_text());draft=folder/draftname;data=draft.read_bytes();text=data.decode();expected=d.get('draft_sha256',d.get('entire_draft_sha256',d.get('prepared_destination_sha256')));assert expected and sha(data)==expected,('Peered entire draft changed',stem);parent=parents[stem];srcpath=parent['fixed_ordinary_Git_source_path'];raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show','47cef49895832e3bfe492f66e1f2ac68785187dd:'+srcpath]);assert sha(raw)==parent['whole_source_sha256']
 if kind=='row':chunks=d['original_payload_chunks']
 elif kind=='tangent':chunks=[x['complete_original_chunk']for x in d['selected_complete_chunks']]
 elif kind=='principal':chunks=[x['original_selected_source']for x in d['complete_original_declarations']]
 elif kind=='drop':chunks=[(folder/d['selected_original_payload']).read_text()]
 elif kind=='coefficient':chunks=[(folder/x['payload']).read_text()for x in d['complete_original_declarations']]
 else:raise AssertionError(kind)
 for chunk in chunks:assert raw.decode().count(chunk)==1,(stem,chunk[:60]);assert text.count(relocate(chunk))==1,(stem,chunk[:60])
 chunks.sort(key=lambda chunk:text.index(relocate(chunk)));layout=[];pos=0
 for i,chunk in enumerate(chunks):
  canonical=relocate(chunk);at=text.index(canonical,pos);context=text[pos:at]
  if context:
   assert not re.search(r'^\s*(?:private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|example)\s',context,re.M),('Unselected declaration in context',stem,context)
   layout.append({'canonical_administrative_context':context,'sha256':sha(context.encode())})
  layout.append({'original_payload_index':i});pos=at+len(canonical)
 context=text[pos:]
 if context:layout.append({'canonical_administrative_context':context,'sha256':sha(context.encode())})
 rebuilt=''.join(relocate(chunks[p['original_payload_index']])if'original_payload_index'in p else p['canonical_administrative_context']for p in layout);assert rebuilt==text
 dest=d.get('destination_module',d.get('destination_module_suggestion',d.get('proposed_public_module','Hironaka.Support.'+draft.stem)))
 nameset=[x['actual_original_declaration']for x in parent['complete_ordinary_original_declarations']]
 assert len(chunks)==len(nameset),(stem,len(chunks),len(nameset))
 out={'source_module':parent['actual_native_parent'],'source_path':srcpath,'source_sha256':sha(raw),'published_source_revision':'47cef49895832e3bfe492f66e1f2ac68785187dd','source_also_byte_identical_at_base':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','destination_module':dest,'destination_path':dest.replace('.','/')+'.lean','complete_original_declarations':nameset,'original_payload_chunks':chunks,'original_selected_source':'\n'.join(chunks),'original_selected_sha256':sha('\n'.join(chunks).encode()),'canonical_source_layout':layout,'imports':re.findall(r'^import ([\w.]+)',text,re.M),'prepared_destination_sha256':sha(data),'original_draft_path':str(draft.relative_to(A)),'original_draft_sha256':sha(data),'independent_extraction_contract':str(c.relative_to(A)),'independent_extraction_contract_sha256':sha(c.read_bytes()),'proof_type_payload_edits':0}
 plans.append(out)
assert len(plans)==10 and sum(len(r['complete_original_declarations'])for r in plans)==40
(P/'plan-before-import-closure.json').write_text(json.dumps(plans,indent=2)+'\n')
print(json.dumps({'status':'TEN_DRAFTS_NORMALIZED_PAYLOADS_ONLY_NOT_INSTALLED','support_files':len(plans),'complete_original_declarations':40,'plan':str(P/'plan-before-import-closure.json')},indent=2))
