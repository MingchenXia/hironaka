"""Prepare audited exact original support selections; no production source writes."""
from pathlib import Path
import json,hashlib,subprocess,re,ast,sys
A=Path(__file__).resolve().parent;R=A.parents[1];O=A/'new-original-prerequisite-extracts';rev='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07';sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['', '2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])');f=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(f.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(f),'exec'),env);relocate=env['relocate']
rows=json.loads((O/'plan.json').read_text());assert len(rows)==3
rows.append(json.loads((O/'fourth-extract-plan-PENDING.json').read_text()))
items=[
 ('EmbeddedOriginalRegularPrefixExact','EmbeddedFromResolution','support-prep/tangent-stopped-prefix','extraction-audit.json',['mem_maxLocus_iff_of_centresAvoid','not_centresAvoid_of_cosupp_eq_empty'],None),
 ('NormalCrossingsWellFormedSublistOriginalExact','NormalCrossingsComparison','support-prep/principal-nc-withe','plan.json',['isWellFormed_withE'],None),
 ('RestrictEmptyTowerAppendOriginalExact','RestrictEmptyTower','support-prep/tangent-restrict-append','extraction-audit.json',['centresAvoid_append_iff'],None),
 ('IrreducibleFullDimensionOpenOriginalExact','AnalyticIrreducibleComponents','support-prep/root-irred-open','extraction-audit.json',['isOpen_of_forall_regularAtDim_self'],None),
 ('CompactBlowupSurjectiveOriginalExact','StrictTransformComposition','support-prep/root-compact-surjective','extraction-audit.json',['surjective_of_isBlowupAlong','IsBlowupSequence.compactSpace_surjective'],None)]
for key,parent,folder,audit,declnames,_ in items:
 folder=A/folder;meta=json.loads((folder/audit).read_text());draft=(folder/(key+'.lean')).read_text();module='TranscendentalNakamaye.Pending.'+parent;source_path='TranscendentalNakamaye/'+module.replace('.','/')+'.lean';raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',rev+':'+source_path]);text=raw.decode()
 if 'original_payload_chunks'in meta:chunks=meta['original_payload_chunks']
 elif 'original_selected_source'in meta:chunks=[meta['original_selected_source']]
 else:
  chunks=[]
  for name in declnames:
   p=folder/(name+'.original.lean.txt')
   if p.exists():chunks.append(p.read_text())
   else:raise AssertionError(('No exact payload capture',p))
 layout=[];pos=0
 for i,body in enumerate(chunks):
  assert text.count(body)==1,(key,'original whole payload not once')
  canonical=relocate(body);assert draft.count(canonical)==1,(key,'complete canonical payload not once')
  at=draft.index(canonical);assert at>=pos
  context=draft[pos:at];assert not re.search(r'^\s*(?:private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|example)\s',context,re.M),(key,context)
  layout.append({'canonical_administrative_context':context,'sha256':sha(context.encode())});layout.append({'original_payload_index':i});pos=at+len(canonical)
 context=draft[pos:];assert not re.search(r'^\s*(?:private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|example)\s',context,re.M)
 layout.append({'canonical_administrative_context':context,'sha256':sha(context.encode())})
 assert ''.join(p.get('canonical_administrative_context',relocate(chunks[p['original_payload_index']])if 'original_payload_index'in p else'')for p in layout)==draft
 r={'destination_module':'Hironaka.Support.'+key,'destination_path':'Hironaka/Support/'+key+'.lean','source_module':module,'source_path':source_path,'published_source_revision':rev,'source_sha256':sha(raw),'complete_original_declarations':[module+'.'+n for n in declnames],'original_selected_source':'\n'.join(chunks),'original_payload_chunks':chunks,'original_selected_sha256':sha('\n'.join(chunks).encode()),'canonical_source_layout':layout,'original_context_audit':str((folder/audit).relative_to(A)),'imports':re.findall(r'^import ([\w.]+)',draft,re.M),'prepared_destination_sha256':sha(draft.encode()),'proof_type_payload_edits':0,'production_installation_pending':True}
 (O/(key+'-whole-original.lean.txt')).write_bytes(raw);(O/(key+'-selected-original.lean.txt')).write_text(r['original_selected_source']);(O/(key+'.lean')).write_text(draft);rows.append(r)
assert len(rows)==9
(O/'plan-attempt04-PENDING.json').write_text(json.dumps(rows,indent=2)+'\n');print('Prepared exact ordinary Git replay plan for',len(rows),'original-support modules; production files unchanged.')
