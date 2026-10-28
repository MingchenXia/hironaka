from pathlib import Path
import json,hashlib,ast,importlib.util,re,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent.parent; D=A.parents[1]
p=json.loads((A/'plan.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('independent_frozen_map',A/'frozen-tools/upstream_namespace_map.py')
names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
node=next(n for n in ast.parse((A/'frozen-tools/verify_incremental_source.py').read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
scope={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[node],type_ignores=[]),'frozen-relocate','exec'),scope)
relocate=scope['relocate'];header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
results=[]
def adjustments(text,row):
 for x in row.get('administrative_elaboration_contexts',[]):
  assert text.count(x['before'])==1;xtext=text.replace(x['before'],x['after']);text=xtext
 return text
for row in p['source_modules']:
 raw=(A/row['raw_capture']).read_bytes();assert sha(raw)==row['source_sha256']
 out=header+relocate(raw.decode());assert sha(out.encode())==row['initial_synchronized_destination_sha256']
 if row['additional_pure_support_imports']:
  at=re.search(r'^import ',out,re.M).start();out=out[:at]+''.join('import '+m+'\n' for m in row['additional_pure_support_imports'])+out[at:]
 out=adjustments(out,row);assert (D/row['destination_path']).read_bytes()==out.encode();assert sha(out.encode())==row['destination_sha256']
 results.append(row['destination_path'])
for row in p.get('support_extracts',[]):
 raw=(A/row['source_parent_capture']).read_bytes();assert sha(raw)==row['source_parent_sha256'];text=row['original_context_segments'][0]
 for i,c in enumerate(row['selected_original_declarations']):
  lo,hi=c['inclusive_lines'];part=''.join(raw.decode().splitlines(keepends=True)[lo-1:hi]);assert part==c['original_text'];assert sha(part.encode())==c['sha256'];text+=part+row['original_context_segments'][i+1]
 out=header+'import '+row['original_import']+'\n\nset_option autoImplicit false\nset_option linter.unusedSectionVars false\n\n'+relocate(text)
 assert sha(out.encode())==row['draft_sha256']
 for extra in row['additional_pure_support_imports']:
  at=re.search(r'^import ',out,re.M).start();out=out[:at]+'import '+extra+'\n'+out[at:]
 out=adjustments(out,row);assert (D/row['destination_path']).read_bytes()==out.encode();assert sha(out.encode())==row['destination_sha256'];results.append(row['destination_path'])
for row in p['blueprints']:
 raw=(A/row['raw_capture']).read_bytes();assert sha(raw)==row['source_sha256'];out=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
 for adj in row['metadata_adjustments']:
  assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
 assert (D/row['destination_path']).read_bytes()==out.encode();assert sha(out.encode())==row['destination_sha256'];results.append(row['destination_path'])
receipt={'status':'PASS_CANONICAL_FIDELITY','source_files':len(p['source_modules']),'support_files':len(p.get('support_extracts',[])),'whole_blueprints':len(p['blueprints']),'plan_sha256':sha((A/'plan.json').read_bytes()),'verified_paths':results,'compiler_used':False}
(A/'independent/fidelity.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='verified_paths'}))
