"""Second immutable ordinary-Git cohort; whole source/proof payloads use frozen rules.

This helper adds the forty independently accepted final45-minus-first5 modules.
It does not change the fixed first cohort, frozen profiles, or comparator.
"""
from pathlib import Path
import hashlib,json,re,subprocess
REVISION='47cef49895832e3bfe492f66e1f2ac68785187dd'
sha=lambda b:hashlib.sha256(b).hexdigest()
class Cohort:
 def __init__(self,A,DST,git,relocate,names,annotate,HEADER):
  self.A,self.DST,self.git,self.relocate,self.names,self.annotate,self.HEADER=A,DST,git,relocate,names,annotate,HEADER
  self.P=A/'additive40-frozen-preparation'
  self.mods=json.loads((self.P/'module-provenance-plan.json').read_text());self.bps=json.loads((self.P/'blueprint-provenance-plan.json').read_text())
  self.contexts=json.loads((A/'additive40-original-elaboration-contexts.json').read_text())['contexts']
  self.imports=json.loads((A/'additive40-original-support-imports.json').read_text())['imports'] if(A/'additive40-original-support-imports.json').exists()else{}
  self.plan=json.loads((A/'additive40-original-prerequisite-extracts/plan.json').read_text()) if(A/'additive40-original-prerequisite-extracts/plan.json').exists()else[]
  assert len(self.mods)==len(self.bps)==40
  assert subprocess.check_output(git+['rev-parse',REVISION],text=True).strip()==REVISION
 def show(self,path):return subprocess.check_output(self.git+['show',REVISION+':'+path])
 def blueprints(self,install,external,unbound,typography):
  records=[]
  for r in self.bps:
   raw=self.show(r['source_path']);assert sha(raw)==r['source_sha256']
   out=self.names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
   for op in typography.get(Path(r['destination_path']).name,[]):assert out.count(op['before'])==1;out=out.replace(op['before'],op['after'])
   out=self.annotate(out,external,unbound)
   assert sha(out.encode())==r['destination_sha256'] and out==(self.P/r['candidate_path']).read_text(),r['destination_path']
   install(r['destination_path'],out)
   records.append({'published_source_revision':REVISION,'immutable_base_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','source_path':r['source_path'],'source_sha256':sha(raw),'destination_path':r['destination_path'],'destination_sha256':sha(out.encode()),'nodes':len(re.findall(r'\\label\{',out)),'proofs':out.count('\\begin{proof}'),'definitions':out.count('\\begin{definition}'),'original_bindings':r['original_bindings'],'local_bindings':r['local_bindings'],'whole_original_chapter_preserved':True,'proof_text_edits':0,'additive_fixed_cohort':True})
  assert sum(r['proofs']for r in records)==122
  return records
 def sources(self,install):
  records=[]
  for r in self.mods:
   raw=self.show(r['source_path']);assert sha(raw)==r['source_sha256']
   out=initial=self.HEADER+self.relocate(raw.decode());assert sha(out.encode())==r['destination_sha256'] and out==(self.P/r['candidate_path']).read_text()
   extra=self.imports.get(r['destination_module'],[])
   if extra:
    at=re.search(r'^import ',out,re.M).start();out=out[:at]+''.join('import '+m+'\n'for m in extra)+out[at:]
   for adj in self.contexts.get(r['destination_module'],[]):assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
   prior=[]
   if(self.A/'additive40-approved-before-sources.json').exists():
    for x in json.loads((self.A/'additive40-approved-before-sources.json').read_text()).get(r['destination_path'],[]):
     b=(self.A/x['path']).read_bytes();assert sha(b)==x['sha256'];prior.append(b)
   install(r['destination_path'],out,prior)
   records.append({'published_source_revision':REVISION,'immutable_base_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','source_module':r['source_module'],'source_path':r['source_path'],'source_sha256':sha(raw),'destination_module':r['destination_module'],'destination_path':r['destination_path'],'initial_synchronized_destination_sha256':sha(initial.encode()),'administrative_elaboration_contexts':self.contexts.get(r['destination_module'],[]),'additional_pure_support_imports':extra,'destination_sha256':sha(out.encode()),'original_proof_tokens_changed':False,'whole_original_source_preserved':True,'additive_fixed_cohort':True})
  for s in self.plan:
   raw=self.show(s['source_path']);assert sha(raw)==s['source_sha256']
   chunks=s['original_payload_chunks'];assert '\n'.join(chunks)==s['original_selected_source']
   for chunk in chunks:assert raw.decode().count(chunk)==1
   out=''
   for piece in s['canonical_source_layout']:
    if'original_payload_index'in piece:out+=self.relocate(chunks[piece['original_payload_index']])
    else:
     context=piece['canonical_administrative_context'];assert sha(context.encode())==piece['sha256']
     assert not re.search(r'^\s*(?:private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|example)\s',context,re.M)
     out+=context
   for adj in self.contexts.get(s['destination_module'],[]):assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
   assert sha(out.encode())==s['prepared_destination_sha256'],s['destination_module'];install(s['destination_path'],out)
   records.append({'published_source_revision':REVISION,'source_module':s['source_module'],'source_path':s['source_path'],'source_sha256':sha(raw),'destination_module':s['destination_module'],'destination_path':s['destination_path'],'initial_synchronized_destination_sha256':sha(out.encode()),'administrative_elaboration_contexts':self.contexts.get(s['destination_module'],[]),'additional_pure_support_imports':s['imports'],'destination_sha256':sha(out.encode()),'original_proof_tokens_changed':False,'supplementary_prerequisite_only':True,'additive_fixed_cohort':True,'complete_original_parent_complement':{'kind':'complete_missing_original_complement','complete_original_declarations':s['complete_original_declarations'],'original_selected_sha256':s['original_selected_sha256'],'whole_original_source_sha256':s['source_sha256'],'old_sources_unchanged':True}})
  return records
 def all_native_modules(self):
  files=subprocess.check_output(self.git+['ls-tree','-r','--name-only',REVISION,'--','TranscendentalNakamaye/TranscendentalNakamaye'],text=True).splitlines()
  return[x.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.')for x in files if x.endswith('.lean')]
