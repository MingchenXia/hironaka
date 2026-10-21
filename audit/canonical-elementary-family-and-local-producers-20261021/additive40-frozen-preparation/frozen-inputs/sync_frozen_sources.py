#!/usr/bin/env python3
"""Exact accepted native source/blueprint relocation through frozen release rules.

Complete source-facing chapters are installed BEFORE any Lean sources. Existing
mathematical sources and chapters are never overwritten. Hironaka.lean and the
extension master receive only recorded append-only imports/inputs. The same
script --check can replay against ordinary published native Git at --revision;
all actual source hashes must match the immutable accepted checkpoint.
"""
from pathlib import Path
import argparse, ast, hashlib, json, re, subprocess, sys
sys.dont_write_bytecode = True
A=Path(__file__).resolve().parent
DST=A.parents[1]
CHECKPOINT='82934a028fb2c94d5a706bf66343fd4614e8a884'
PUBLISHED_REVISION='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
HEADER='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
FROZEN='audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
sha=lambda raw:hashlib.sha256(raw).hexdigest()


def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--source-root',type=Path,required=True)
 p.add_argument('--revision',default=PUBLISHED_REVISION)
 p.add_argument('--ledger',action='store_true',help='Authoring only; final published-source replay uses ordinary Git')
 p.add_argument('--check',action='store_true')
 args=p.parse_args()
 assert re.fullmatch('[0-9a-f]{40}',args.revision)
 git=['git',f'--git-dir={args.source_root}/.archon-horizon/vcs/workspace.git',f'--work-tree={args.source_root}'] if args.ledger else ['git','-C',str(args.source_root)]
 assert subprocess.check_output(git+['rev-parse',args.revision],text=True).strip()==args.revision
 def show(path):return subprocess.check_output(git+['show',args.revision+':'+path])
 def batch(paths):
  data=subprocess.check_output(git+['cat-file','--batch'],input=''.join(args.revision+':'+x+'\n'for x in paths).encode())
  pos=0;result={}
  for path in paths:
   end=data.index(b'\n',pos);head=data[pos:end].split();assert len(head)==3 and head[1]==b'blob',(path,head)
   pos=end+1;size=int(head[2]);result[path]=data[pos:pos+size];pos+=size+1
  assert pos==len(data)
  return result
 def save(path,obj):
  raw=(json.dumps(obj,indent=2)+'\n').encode()
  if args.check:assert (A/path).read_bytes()==raw,path
  else:(A/path).write_bytes(raw)
 def install(path,raw,before=None):
  dest=DST/path;raw=raw.encode()if isinstance(raw,str)else raw
  if args.check:assert dest.read_bytes()==raw,path
  elif dest.exists():
   current=dest.read_bytes()
   if current==raw:return
   candidates=before if isinstance(before,list)else[before]
   assert any(x is not None and current==x for x in candidates),('Refuse overwrite',path)
   dest.write_bytes(raw)
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw)
 plan=json.loads((A/'initial-port-plan.json').read_text())
 guard=plan['existing_destination_math_source_digests'];bpguard=plan['existing_blueprint_tex_digests']
 for path,h in guard.items():assert sha((DST/path).read_bytes())==h,path
 for path,h in plan['toolchain_profiles'].items():assert sha((DST/path).read_bytes())==h,('Frozen profile changed',path)
 sys.path.insert(0,str(DST/'scripts'))
 import upstream_namespace_map as names
 from upstream_blueprint_scope import annotate
 names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
 flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
 frozen=(DST/FROZEN).read_text();fn=next(n for n in ast.parse(frozen).body if isinstance(n,ast.FunctionDef)and n.name=='relocate')
 env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(DST/FROZEN),'exec'),env);relocate=env['relocate']
 inventories=[('native486','TranscendentalNakamaye/audit/hironaka-subgoals-486-20261018/regular-main-v52-inventory.json'),('phase1','TranscendentalNakamaye/audit/hironaka-all-nine-20261020/independent/twenty-one-new-independent-manifest.json'),('phase2','TranscendentalNakamaye/audit/hironaka-all-nine-phase2-20261020/checkpoint-145/evidence/work/g1-g9-20261020-phase2/independent/phase2-145-modules-independent-manifest.json'),('phase3','TranscendentalNakamaye/audit/hironaka-all-nine-phase3-20261021/checkpoint-5/evidence/work/g1-g9-20261021-phase3/independent/phase3-5-modules-independent-manifest.json')]
 cohorts={};inventory_records=[];roots=set();verified_rows={}
 for cohort,path in inventories:
  raw=show(path);obj=json.loads(raw);mods=obj['modules']
  if cohort!='native486':
   for item in mods:verified_rows[item['module']]=item
   mods=[x['module']for x in mods]
  cohorts[cohort]=sorted(mods);roots.update(mods);inventory_records.append({'cohort':cohort,'path':path,'sha256':sha(raw),'modules':len(mods)})
 assert {k:len(v)for k,v in cohorts.items()}=={'native486':486,'phase1':21,'phase2':145,'phase3':5}
 imp=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',re.M)
 seen=set();ordered=[];present=[]
 def visit(m):
  if m in seen:return
  seen.add(m);dst=names.new_mod(m).replace('.','/')+'.lean'
  if dst in guard:present.append(m);return
  path='TranscendentalNakamaye/'+m.replace('.','/')+'.lean';raw=show(path)
  if m in verified_rows:assert sha(raw)==verified_rows[m]['source']['sha256'],m
  for i in imp.findall(raw.decode()):
   if i.startswith('TranscendentalNakamaye.'):visit(i)
  ordered.append((m,path,raw))
 for m in sorted(roots):visit(m)
 assert len(ordered)==316 and len(set(m for m,_,_ in ordered)&roots)==281
 external=json.loads((DST/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((DST/'scripts/upstream_blueprint_unbound_bindings.json').read_text());typography=json.loads((DST/'scripts/upstream_blueprint_typography.json').read_text())
 from blueprint_documentation_overlay import chapter as metadata_chapter,external_index,PLAN as documentation_plan
 from blueprint_original_node_extracts import chapter as original_node_extract,PLAN as node_extract_plan
 assert documentation_plan['native_revision']==PUBLISHED_REVISION
 bppaths=[x for x in subprocess.check_output(git+['ls-tree','-r','--name-only',args.revision,'--','TranscendentalNakamaye/blueprint/src'],text=True).splitlines()if x.endswith('.tex')]
 newmods={m for m,_,_ in ordered};bp_records=[];bp_existing=[]
 # Every complete new source-facing blueprint is installed before the first Lean source.
 for path,raw in batch(bppaths).items():
  text=raw.decode();binds=[x.strip()for group in re.findall(r'\\lean\{([^}]+)\}',text)for x in group.split(',')]
  dst='blueprint/'+Path(path).name
  if dst not in node_extract_plan['extracts']and not any(any(x.startswith(m+'.')for m in newmods)for x in binds):continue
  if dst in bpguard:
   assert sha((DST/dst).read_bytes())==bpguard[dst],dst
   bp_existing.append({'source_path':path,'source_sha256':sha(raw),'destination_path':dst,'existing_destination_sha256':bpguard[dst],'preserved_existing_chapter':True});continue
  out=names.rename_text_names(text).replace('\\chapter{','\\section{')
  for adj in typography.get(Path(dst).name,[]):assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
  out=annotate(out,external,unbound);out=original_node_extract(dst,out);initial_bp=out;out=metadata_chapter(dst,out);install(dst,out)
  for m,row in verified_rows.items():
   if row['blueprint']['path']==path:assert sha(raw)==row['blueprint']['sha256'],path
  bp_record={'accepted_checkpoint':CHECKPOINT,'published_source_revision':PUBLISHED_REVISION,'source_path':path,'source_sha256':sha(raw),'destination_path':dst,'destination_sha256':sha(out.encode()),'nodes':len(re.findall(r'\\label\{',out)),'proofs':out.count('\\begin{proof}'),'definitions':out.count('\\begin{definition}'),'original_bindings':binds,'local_bindings':[x.strip()for group in re.findall(r'\\lean\{([^}]+)\}',out)for x in group.split(',')]}
  if initial_bp!=out:bp_record.update(initial_synchronized_destination_sha256=sha(initial_bp.encode()),documentation_metadata_overlay=[x for x in documentation_plan['label_disambiguations']if x['destination_path']==dst],proof_text_edits=0)
  if dst in node_extract_plan['extracts']:
   selection=node_extract_plan['extracts'][dst];bp_record.update(complete_original_node_extract=selection,whole_parent_original_bindings=binds,original_bindings=[x for node in selection['complete_original_node_ranges']for x in node['original_bindings']])
  bp_records.append(bp_record)
 for path,raw in batch([x['native_path']for x in documentation_plan['external_original_sources'].values()]).items():
  expected=next(x['sha256']for x in documentation_plan['external_original_sources'].values()if x['native_path']==path);assert sha(raw)==expected,path
 extra_documentation_path=documentation_plan['external_index_path'];install(extra_documentation_path,external_index())
 master0=(A/'previous-extensions.tex').read_bytes()if(A/'previous-extensions.tex').exists()else(DST/'blueprint/extensions.tex').read_bytes()
 assert sha(master0)==bpguard['blueprint/extensions.tex']
 if not args.check:(A/'previous-extensions.tex').write_bytes(master0)
 master=master0.decode();anchor='\\begin{thebibliography}{99}';assert master.count(anchor)==1
 inputs=[Path(r['destination_path']).stem for r in bp_records]+[Path(extra_documentation_path).stem];assert all('\\input{'+x+'}'not in master for x in inputs)
 block=''.join('\\input{'+x+'}\n'for x in inputs);master=master.replace(anchor,block+anchor)
 master_before=[master0]
 if (A/'blueprint-support-node-expansion/previous-master.json').exists():
  prior=json.loads((A/'blueprint-support-node-expansion/previous-master.json').read_text())
  captured=(A/prior['capture']).read_bytes();assert sha(captured)==prior['sha256'];master_before.append(captured)
 install('blueprint/extensions.tex',master,master_before)
 additional=json.loads((DST/'scripts/upstream_additional_imports.json').read_text());contexts=json.loads((DST/'scripts/upstream_elaboration_contexts.json').read_text());records=[]
 new_context_file=A/'new-original-elaboration-contexts.json'
 new_import_file=A/'new-original-support-imports.json'
 new_contexts=json.loads(new_context_file.read_text())['contexts']if new_context_file.exists()else{}
 new_imports=json.loads(new_import_file.read_text())['imports']if new_import_file.exists()else{}
 restoration=A/'new-source-context-restoration/preflight.json'
 restoration_before=json.loads(restoration.read_text())['sources']if restoration.exists()else{}
 complement_plan=json.loads((A/'parent-complement-plan.json').read_text())if(A/'parent-complement-plan.json').exists()else{}
 for m,path,raw in ordered:
  newm=names.new_mod(m);dst=newm.replace('.','/')+'.lean';out=initial=HEADER+relocate(raw.decode());adjustments=contexts.get(newm,[])
  for adj in adjustments:assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
  extras=[*additional.get(newm,[]),*new_imports.get(newm,[])]
  pending_supplement_names={x['destination_module']for x in json.loads((A/'new-original-prerequisite-extracts/plan.json').read_text())}if new_import_file.exists()else set()
  for extra in extras:assert(DST/(extra.replace('.','/')+'.lean')).is_file()or extra in pending_supplement_names,extra
  if extras:
   first=re.search(r'^import ',out,re.M);assert first
   out=out[:first.start()]+''.join('import '+extra+'\n'for extra in extras)+out[first.start():]
  complement=complement_plan.get(dst)
  if complement:
   assert sha(out.encode())==complement['initial_whole_copy_sha256'],dst
   reuse=complement['reuse_original_support_imports']
   for owner in reuse:assert owner.replace('.','/')+'.lean'in guard,owner
   if complement['kind']=='pure_existing_support_imports':out=HEADER+''.join('import '+owner+'\n'for owner in reuse)
   else:
    for dec in complement.get('remove_complete_already_existing_declarations',[]):
     body=dec['canonical_source'];assert sha(body.encode())==dec['sha256']and out.count(body)==1,(dst,dec['name']);out=out.replace(body,'',1)
    if'remove_existing_original_context_and_declarations'in complement:
     body=complement['remove_existing_original_context_and_declarations'];assert out.count(body)==1;out=out.replace(body,'',1)
    addition=''.join('import '+owner+'\n'for owner in reuse)
    at=out.index('import ')if complement['import_position']=='before_original_imports'else list(re.finditer(r'^import [^\n]+\n',out,re.M))[-1].end()
    out=out[:at]+addition+out[at:]
   assert sha(out.encode())==complement['destination_sha256'],dst
  for adj in new_contexts.get(newm,[]):assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
  previous=None
  if dst in restoration_before:
   pre=restoration_before[dst];previous=[(A/pre['before_capture']).read_bytes()];assert sha(previous[0])==pre['before_sha256']
   for capture in pre.get('approved_intermediate_captures',[]):
    captured=(A/capture['path']).read_bytes();assert sha(captured)==capture['sha256'];previous.append(captured)
  install(dst,out,previous);record={'accepted_checkpoint':CHECKPOINT,'published_source_revision':PUBLISHED_REVISION,'source_module':m,'source_path':path,'source_sha256':sha(raw),'destination_module':newm,'destination_path':dst,'initial_synchronized_destination_sha256':sha(initial.encode()),'administrative_elaboration_contexts':[*adjustments,*new_contexts.get(newm,[])],'additional_pure_support_imports':extras,'destination_sha256':sha(out.encode()),'original_proof_tokens_changed':False}
  if complement:record['complete_original_parent_complement']=complement
  records.append(record)
 if new_import_file.exists():
  for supplement in json.loads((A/'new-original-prerequisite-extracts/plan.json').read_text()):
   raw=show(supplement['source_path']);assert sha(raw)==supplement['source_sha256']
   chunks=supplement['original_payload_chunks']
   assert '\n'.join(chunks)==supplement['original_selected_source']
   for body in chunks:assert raw.decode().count(body)==1,('Original complete payload changed',supplement['destination_module'])
   if 'canonical_source_layout' in supplement:
    out=''
    for piece in supplement['canonical_source_layout']:
     if 'original_payload_index' in piece:out+=relocate(chunks[piece['original_payload_index']])
     else:
      context=piece['canonical_administrative_context']
      assert sha(context.encode())==piece['sha256']
      assert not re.search(r'^\s*(?:private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|example)\s',context,re.M),('Unselected declaration in support context',supplement['destination_module'])
      out+=context
   else:
    out='/- Complete original prerequisite; statement and mathematical proof unchanged. -/\n'+''.join('import '+m+'\n'for m in supplement['imports'])+'\n'+relocate(supplement['original_context']+supplement['original_selected_source']+supplement['original_closing'])
    for adj in supplement.get('administrative_contexts',[]):assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
    if 'StepOneCanonicalStepDrop' in supplement['destination_module']:
     out=out.replace('/- Complete original prerequisite; statement and mathematical proof unchanged. -/','/- Complete original prerequisites; statements and mathematical proofs unchanged. -/',1)
   assert sha(out.encode())==supplement['prepared_destination_sha256'],supplement['destination_module']
   previous=None
   if 'approved_administrative_before_capture'in supplement:
    prior=supplement['approved_administrative_before_capture'];previous=(A/prior['path']).read_bytes();assert sha(previous)==prior['sha256']
   install(supplement['destination_path'],out,previous)
   records.append({'accepted_checkpoint':CHECKPOINT,'published_source_revision':PUBLISHED_REVISION,'source_module':supplement['source_module'],'source_path':supplement['source_path'],'source_sha256':supplement['source_sha256'],'destination_module':supplement['destination_module'],'destination_path':supplement['destination_path'],'initial_synchronized_destination_sha256':sha(out.encode()),'administrative_elaboration_contexts':[],'additional_pure_support_imports':supplement['imports'],'destination_sha256':sha(out.encode()),'original_proof_tokens_changed':False,'supplementary_prerequisite_only':True,'complete_original_parent_complement':{'kind':'complete_missing_original_complement','complete_original_declarations':supplement['complete_original_declarations'],'original_selected_sha256':supplement['original_selected_sha256'],'whole_original_source_sha256':supplement['source_sha256'],'old_sources_unchanged':True}})
 root0=(A/'previous-Hironaka.lean').read_bytes()if(A/'previous-Hironaka.lean').exists()else(DST/'Hironaka.lean').read_bytes()
 if not args.check:(A/'previous-Hironaka.lean').write_bytes(root0)
 root=root0.decode();marker=root.find('/-!');assert marker>=0
 imports=[r['destination_module']for r in records if r['source_module']in roots and not r.get('supplementary_prerequisite_only')];assert all(('import '+m+'\n')not in root for m in imports)
 rootblock=''.join('import '+m+'\n'for m in imports)+'\n';root=root[:marker]+rootblock+root[marker:];install('Hironaka.lean',root,root0)
 for path,h in guard.items():assert sha((DST/path).read_bytes())==h,path
 for path,h in bpguard.items():
  if path!='blueprint/extensions.tex':assert sha((DST/path).read_bytes())==h,path
 save('provenance.json',records);save('blueprint-provenance.json',bp_records);save('existing-blueprint-preservation.json',bp_existing)
 allsourcepaths=[x for x in subprocess.check_output(git+['ls-tree','-r','--name-only',args.revision,'--','TranscendentalNakamaye/TranscendentalNakamaye'],text=True).splitlines()if x.endswith('.lean')]
 allmods=[x.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.')for x in allsourcepaths]
 for fn,txt in [('core-old-modules.tsv',''.join(r['source_module']+'\t'+r['destination_module']+'\n'for r in records)),('core-new-modules.tsv',''.join(r['destination_module']+'\t'+r['destination_module']+'\n'for r in records)),('exact-module-renames.tsv',''.join(m+'\t'+names.new_mod(m)+'\n'for m in allmods if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.'))))]:
  if args.check:assert(A/fn).read_text()==txt,fn
  else:(A/fn).write_text(txt)
 summary={'status':'PASS_EXACT_SOURCE_AND_BLUEPRINT_REPLAY'if args.check else'COMPLETE_SOURCE_AND_BLUEPRINT_RELOCATION_ONLY','accepted_checkpoint':CHECKPOINT,'actual_source_revision':args.revision,'ordinary_git_backend':not args.ledger,'new_source_files':len(records),'base_new_source_files':316,'supplementary_missing_original_prerequisite_extracts':sum(r.get('supplementary_prerequisite_only',False)for r in records),'complete_new_whole_modules':316-len(complement_plan),'complete_missing_original_complements':sum(x['kind']=='complete_missing_original_complement'for x in complement_plan.values()),'pure_existing_support_import_adapters':sum(x['kind']=='pure_existing_support_imports'for x in complement_plan.values()),'missing_accepted_root_modules':len(imports),'accepted_root_union':len(roots),'transitive_only_new_source_files':len(records)-len(imports),'new_complete_blueprint_chapters':len(bp_records)-len(node_extract_plan['extracts']),'new_complete_original_node_extract_chapters':len(node_extract_plan['extracts']),'documentation_only_external_prerequisite_chapters':1,'external_prerequisite_label_anchors':documentation_plan['external_labels'],'new_written_proofs':sum(x['proofs']for x in bp_records),'new_ready_nodes':sum((DST/x['destination_path']).read_text().count('\\leanok')for x in bp_records),'old1159_math_files_preserved':len(guard),'old_blueprint_files_preserved_except_append_only_master':len(bpguard),'original_proof_token_edits':0,'build_kernel_axiom_expression_checked_here':False,'inventory_sources':inventory_records,'cohorts':{k:len(v)for k,v in cohorts.items()}}
 if args.check:(A/'source-replay-receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
 else:save('source-sync-receipt.json',summary)
 save('source-document-integration.json',{'root_before_sha256':sha(root0),'root_after_sha256':sha(root.encode()),'exact_added_import_block':rootblock,'master_before_sha256':sha(master0),'master_after_sha256':sha(master.encode()),'exact_added_input_block':block,'old_math_files_unchanged':len(guard),'old_chapters_unchanged':len(bpguard)-1})
 print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
