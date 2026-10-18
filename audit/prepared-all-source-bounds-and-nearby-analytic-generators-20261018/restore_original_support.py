"""Recover three complete original prerequisites, retaining their actual contexts.

All proof blocks are compiler-ranged substrings of the fixed normal published Git
source. Context pieces have exact original byte offsets. Only explicitly recorded
unavailable imports/irrelevant opens are omitted; no proof text is edited.
"""
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
SOURCE=Path('/workspace/archon-nakamaye-publish');NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
REV='f873b1d904f8e63cd9f73e0b5bf6eefb0332093a';CP='862e555f2c5289f9b29cb844461cda7a23618d7c'
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['','2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'))
configs=[
 ('BlowupTowerSplitIso','TowerIsoBaseCongruenceExact',
  ['IsTowerIso.congr_base'],[(1,63),'IsTowerIso.congr_base','end Congr\n'],[],[]),
 ('HironakaSmoothCentreRealDomainSaturation','RealDomainLocalCoherenceExact',
  ['idealFGAt_of_coherentOn'],[(1,17),'idealFGAt_of_coherentOn'],[],[]),
 ('HironakaSmoothCentreRealDomainInitialRelations','RealDomainOriginDictionaryExact',
  ['mk_mem_originalOriginIdeal_iff_of_local'],[(1,22),'mk_mem_originalOriginIdeal_iff_of_local'],
  ['Hironaka.Support.RealDomainLocalCoherenceExact','Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations'],
  ['  HironakaSmoothCentreRealDomainDeformation'])]

previous=json.loads((HERE/'new-support-provenance.json').read_text()) if (HERE/'new-support-provenance.json').exists() else []
records=[];contexts=[]
for short,dest,selected,pieces,extra_imports,omitted_opens in configs:
 module='TranscendentalNakamaye.Pending.'+short;source_path='TranscendentalNakamaye/'+module.replace('.','/')+'.lean'
 raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+source_path]);text=raw.decode();lines=text.splitlines(keepends=True)
 assert raw==(NATIVE/(module.replace('.','/')+'.lean')).read_bytes()
 ilean=NATIVE/'.lake/build/lib/lean'/(module.replace('.','/')+'.ilean');decls=json.loads(ilean.read_text())['decls']
 destination_module='Hironaka.Support.'+dest;destination_path=destination_module.replace('.','/')+'.lean'
 own=[];blocks={}
 for suffix in selected:
  found=[(n,r) for n,r in decls.items() if n.endswith('.'+suffix)];assert len(found)==1
  name,r=found[0];sl,sc,el,ec=r[:4];start=len(''.join(lines[:sl]))+sc;end=len(''.join(lines[:el]))+ec
  block=text[start:end];assert text.count(block)==1;blocks[suffix]=(start,end)
  sidecar=dest+'-'+suffix+'-original.lean.txt';(HERE/sidecar).write_text(block)
  own.append({'source_revision':CP,'published_source_revision':REV,'source_module':module,'source_path':source_path,
   'source_parent_sha256':sha(raw),'compiler_ilean_sha256':sha(ilean.read_bytes()),'actual_original_declaration':name,
   'compiler_source_range':r[:4],'source_byte_range':[len(text[:start].encode()),len(text[:end].encode())],
   'source_complete_declaration_file':sidecar,'source_complete_declaration_sha256':sha(block.encode()),
   'destination_module':destination_module,'destination_path':destination_path})
 spans=[]
 for piece in pieces:
  if isinstance(piece,tuple):a,b=piece;spans.append((len(''.join(lines[:a-1])),len(''.join(lines[:b]))))
  elif piece in blocks:spans.append(blocks[piece])
  else:assert text.count(piece)==1;start=text.index(piece);spans.append((start,start+len(piece)))
 footer=re.search(r'(?m)^end\n\n?end '+re.escape(module)+r'\n?$',text)
 assert footer is not None;spans.append(footer.span())
 original_pieces=[{'source_byte_range':[len(text[:a].encode()),len(text[:b].encode())],
  'original_text':text[a:b],'sha256':sha(text[a:b].encode())} for a,b in spans]
 joined='\n\n'.join(r['original_text'] for r in original_pieces)
 for suffix,(a,b) in blocks.items():assert joined.count(text[a:b])==1,(dest,suffix)
 changes=[]
 for line in joined.splitlines(keepends=True):
  if line.startswith('import TranscendentalNakamaye.'):
   m=line.removeprefix('import ').strip()
   try:mapped=names.new_mod(m)
   except ValueError:mapped=None
   if mapped is None or not (ROOT/(mapped.replace('.','/')+'.lean')).exists():
    changes.append({'before':line,'after':'','reason':'Original import is unavailable in the pure public library and contributes no selected proof declaration; required geometric originals are recovered separately.'})
 for opening in omitted_opens:
  changes.append({'before':opening,'after':'','reason':'Unrelated original real-domain deformation namespace is unavailable; no selected type or proof uses it.'})
 out=joined
 for change in changes:
  assert out.count(change['before'])==1
  assert all(change['before'] not in text[a:b] for a,b in blocks.values())
  out=out.replace(change['before'],change['after'])
 out='/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/\n'+''.join('import '+m+'\n' for m in extra_imports)+relocate(out)
 p=ROOT/destination_path
 if p.exists():
  old=next((r for r in previous if r['destination_path']==destination_path),None)
  assert (old is not None and sha(p.read_bytes())==old['destination_sha256']) or p.read_text()==out
 if not p.exists() or p.read_text()!=out:p.write_text(out)
 for record in own:record['destination_sha256']=sha(out.encode())
 records.extend(own);contexts.append({'source_module':module,'source_path':source_path,'source_parent_sha256':sha(raw),
  'destination_module':destination_module,'destination_path':destination_path,'original_context_pieces':original_pieces,
  'recorded_context_omissions':changes,'pure_existing_imports':extra_imports,'omitted_original_proof_tokens':0,
  'destination_sha256':sha(out.encode())})
(HERE/'new-support-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
(HERE/'original-support-contexts.json').write_text(json.dumps(contexts,indent=2)+'\n')
adjustments={
 'Hironaka.Resolution.HironakaSharpActualCurveUniformPrefixRestriction':[
  {'before':'import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction\n',
   'after':'import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction\nimport Hironaka.Support.TowerIsoBaseCongruenceExact\n',
   'reason':'The preceding public split-tower module omitted the original congr_base proof. Load its complete original declaration and section context without modifying any previous mathematical source.'}],
 'Hironaka.Resolution.HironakaActualAnalyticNearbyVertexGenerators':[
  {'before':'import Hironaka.Resolution.HironakaSmoothCentreRealDomainInitialRelations\n',
   'after':'import Hironaka.Support.RealDomainOriginDictionaryExact\n',
   'reason':'Load the complete original representative dictionary and local-coherence prerequisite with full original contexts; unrelated real-domain deformation results are not dependencies of these selected original proofs.'}]}

instance_contexts=HERE/'original-instance-restorations.json'
if instance_contexts.exists():
 for module,changes in json.loads(instance_contexts.read_text()).items():
  adjustments.setdefault(module,[]).extend(changes)
(HERE/'owned-administrative-contexts.json').write_text(json.dumps(adjustments,indent=2)+'\n')
print(json.dumps({'status':'RESTORED_COMPLETE_ORIGINAL_PROOFS_AND_CONTEXTS','support_modules':len(contexts),'complete_original_declarations':len(records)}))
