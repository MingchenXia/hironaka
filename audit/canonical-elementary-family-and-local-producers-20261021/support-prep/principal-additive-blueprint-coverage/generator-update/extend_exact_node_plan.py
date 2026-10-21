from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
R=Path('/workspace/hironaka');A=R/'audit/canonical-elementary-family-and-local-producers-20261021';W=A/'support-prep/principal-additive-blueprint-coverage';D=W/'generator-update';U=Path('/workspace/archon-publish')
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
oldplan=json.loads((D/'before/blueprint-original-node-extract-plan.json').read_text());oldcode=(D/'before/blueprint_original_node_extracts.py').read_text()
assert (A/'blueprint-original-node-extract-plan.json').read_text()==(D/'before/blueprint-original-node-extract-plan.json').read_text()
assert (A/'blueprint_original_node_extracts.py').read_text()==oldcode
p=json.loads((W/'complete-original-node-integration-plan.json').read_text());ctx=json.loads((W/'authentic-context-and-tail-integration-plan.json').read_text());plan=json.loads(json.dumps(oldplan));rev=plan['native_revision']
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
node=next(x for x in ast.parse(oldcode).body if isinstance(x,ast.FunctionDef) and x.name=='block');env={'re':re};exec(compile(ast.Module(body=[node],type_ignores=[]),'old-original-block','exec'),env);block=env['block']
actual=json.loads((D/'two-actual-original-support-bindings.json').read_text());assert len(actual)==2
for row in actual:assert set(row['transitive_axioms'])=={'propext','Classical.choice','Quot.sound'} and row['actual_physical_CIs_matching_name']==1 and row['actual_full_type_repr']
nativeinventory=A/'native-blueprint-original-binding-inventory.json';nin=json.loads(nativeinventory.read_text());nname='TranscendentalNakamaye.Pending.CoefficientIdealRestriction.N_coeffMarked';nrecord=next(r for r in nin if r['original_binding']==nname)
assert nrecord['status']=='ACTUAL_ORIGINAL_EXPORT_STANDARD_AXIOMS_ONLY' and set(nrecord['transitive_axioms'])=={'propext','Classical.choice','Quot.sound'}
upstream={nname:nrecord,**{r['original_binding']:r for r in actual}}
evidence={'status':'EXPLICIT_UPSTREAM_ONLY_BINDINGS_ACTUAL_NATIVE_WITNESSES_NO_LOCAL_EXPORT_CLAIM','new_query':{'file':'two-actual-original-support-bindings.json','sha256':sha((D/'two-actual-original-support-bindings.json').read_bytes()),'query_source':'CheckTwoActualOriginalSupportBindings.lean','query_source_sha256':sha((D/'CheckTwoActualOriginalSupportBindings.lean').read_bytes()),'exit_code':int((D/'two-native-binding-query.exit').read_text()),'fair_reader_invocations':1,'cold_builds':0,'kernel_replays':0,'full_expression_DAG_exports':0},'bindings':[]}
for n,r in upstream.items():
 source='TranscendentalNakamaye/'+r['actual_owner'].replace('.','/')+'.lean';raw=subprocess.check_output(['git','-C',str(U),'show',rev+':'+source]);current=Path('/workspace/archon-nakamaye')/source;assert current.read_bytes()==raw
 artifact=Path('/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/build/lib/lean')/(r['actual_owner'].replace('.','/')+'.olean');assert artifact.exists()
 evidence['bindings'].append({'original_binding':n,'canonical_public_binding':names.rename_text_names(n),'actual_witness':r,'witness_reused':n==nname,'reused_witness_source':str(nativeinventory.relative_to(A)) if n==nname else None,'reused_witness_file_sha256':sha(nativeinventory.read_bytes()) if n==nname else None,'fixed_revision':rev,'fixed_source_path':source,'fixed_source_sha256':sha(raw),'actual_native_source_byte_equal':True,'actual_existing_artifact':str(artifact),'artifact_sha256':sha(artifact.read_bytes()),'retained_status':'upstreamlean plus mixed/upstreamleanok, never local lean solely from this witness'})
(D/'three-upstream-only-bindings-evidence.json').write_text(json.dumps(evidence,ensure_ascii=False,indent=2)+'\n')
contexts={r['insert_before_label']:r for r in ctx['original_context_before_label_segments']}
newlabels=set(p['minimal_direct_new_complete_nodes']);records={r['label']:r for r in p['node_records']}
for path,group in [('blueprint/maximal-contact.tex','NEW maximal-contact support excerpt'),('blueprint/hironaka.tex','NEW hironaka support excerpt')]:
 spec=plan['extracts'][path];beforelabels=list(spec['labels']);added=p['proposed_new_excerpt_chapter_groups'][group];spec['initial_original_labels']=beforelabels
 spec['labels']+=added;spec['additional_original_node_layout']=[]
 raw=(W/(Path(spec['source_path']).name+'.whole-original.txt')).read_text();assert sha(raw)==spec['source_sha256']
 for label in added:
  rec=records[label];core=block(raw,label);full=(W/rec['full_node_with_native_trailing_prose_capture']).read_text().rstrip('\n');assert full.startswith(core) and raw.count(full)==1
  start=raw.index(full);end=start+len(full);following=full[len(core):]
  layout={'label':label,'following_original_text':following,'following_original_text_sha256':sha(following),'original_complete_start_line':raw.count('\n',0,start)+1,'original_complete_end_line':raw.count('\n',0,end)+1}
  if label in contexts:
   c=contexts[label];layout['context_before']=c['original_text'];layout['context_before_sha256']=c['sha256'];layout['original_context_lines']=c['original_lines']
   assert raw.count(c['original_text'])==1
  spec['additional_original_node_layout'].append(layout)
  binds=[v for v in rec['all_original_attachments']];native=[r['native_name'] for r in binds];nativeup=[n for n in native if n in upstream]
  row={'start_line':raw.count('\n',0,start)+1,'end_line':raw.count('\n',0,end)+1,'environment':rec['environment'],'labels':[label],'complete_written_proof':bool(rec['written_proofs']),'original_bindings':native,'new_source_facing_bindings':[n for n in native if n not in upstream],'new_selected_support_declarations':rec['selected_support_declarations'],'start_offset':start,'end_offset':end,'whole_original_block_sha256':sha(full),'support_extension':True,'extension_cohort':'authorized_additive40_closed40_minimal19','following_original_text_range':{'start_line':raw.count('\n',0,start+len(core))+1,'end_line':raw.count('\n',0,end)+1,'sha256':sha(following)} if following else None}
  if nativeup:row['separately_verified_upstream_bindings']=nativeup;row['actual_original_binding_evidence']='support-prep/principal-additive-blueprint-coverage/generator-update/three-upstream-only-bindings-evidence.json'
  if label=='mc:derivative-marked':row['explicit_definition_justification_tail_override']={'original_lines':[410,411],'complete_original_range':[399,411],'reason':'Genuine original proof paragraph follows end{definition} outside a proof environment; retain it once unchanged.'}
  spec['complete_original_node_ranges'].append(row)
  for n in nativeup:spec['separately_verified_original_bindings'][names.rename_text_names(n)]=n
 spec['selected_complete_proofs']=sum(r['complete_written_proof'] for r in spec['complete_original_node_ranges'])
 spec['selected_definitions']=sum(r['environment']=='definition' for r in spec['complete_original_node_ranges'])
 spec['additional_complete_original_support_proofs']=oldplan['extracts'][path]['additional_complete_original_support_proofs']+sum(records[l]['written_proofs'] for l in added)
 spec['authorized_additive40_extension']={'complete_nodes':len(added),'written_proofs':sum(records[l]['written_proofs'] for l in added),'all_original_attachments_retained':True,'prior_selected_node_records_unchanged':True,'production_generation_pending_root_peer':True,'actual_upstream_binding_witness':'support-prep/principal-additive-blueprint-coverage/generator-update/three-upstream-only-bindings-evidence.json'}
 if path=='blueprint/maximal-contact.tex':
  spec['additional_unchanged_original_hypothesis_contexts']=ctx['original_context_before_label_segments'];spec['explicit_original_tail_overrides']=ctx['explicit_original_tail_overrides']
# Keep all prior thirteen node records and earlier contexts byte-for-byte as JSON values.
for path,spec in oldplan['extracts'].items():
 count=len(spec['complete_original_node_ranges']);assert plan['extracts'][path]['complete_original_node_ranges'][:count]==spec['complete_original_node_ranges']
 if 'unchanged_original_hypothesis_contexts' in spec:assert plan['extracts'][path]['unchanged_original_hypothesis_contexts']==spec['unchanged_original_hypothesis_contexts']
(A/'blueprint-original-node-extract-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
helper='''\ndef append_original_node_layout(result,text,spec):
 # The layout contains only approved complete original nodes, shared native
 # subsection assumptions, and literal original following explanation text.
 for item in spec.get('additional_original_node_layout',[]):
  context=item.get('context_before','')
  if context:
   assert text.count(context)==1,item['label']
   result+='\\n'+context+'\\n'
  payload=block(text,item['label'])
  following=item['following_original_text']
  if following:
   start=text.index(payload)
   assert text.startswith(following,start+len(payload)),item['label']
  result+='\\n'+payload+following+'\\n'
 return result
'''
newcode=oldcode.replace('\ndef chapter(path,text):',helper+'\ndef chapter(path,text):')
oldhir="result='\\\\section{Original well-founded canonical-segment prerequisite}\\n\\n'+'\\n\\n'.join(block(text,label)for label in spec['labels'])+'\\n'"
# Replace only the old hironaka iteration, keeping its existing old node payload/order.
needle="for label in spec['labels'])+'\\n'"
# There are analytic and hironaka occurrences; target exact else branch line.
oldline=next(l for l in oldcode.splitlines() if "Original well-founded canonical-segment prerequisite" in l)
newline=oldline.replace("spec['labels']","spec.get('initial_original_labels',spec['labels'])")
assert newcode.count(oldline)==1;newcode=newcode.replace(oldline,newline)
anchor=' # Established attachment/status metadata only. Every mathematical statement\n'
assert newcode.count(anchor)==1;newcode=newcode.replace(anchor,' result=append_original_node_layout(result,text,spec)\n'+anchor)
(A/'blueprint_original_node_extracts.py').write_text(newcode)
print(json.dumps({'generator_before_sha256':sha(oldcode),'generator_after_sha256':sha(newcode),'plan_before_sha256':sha((D/'before/blueprint-original-node-extract-plan.json').read_bytes()),'plan_after_sha256':sha((A/'blueprint-original-node-extract-plan.json').read_bytes()),'old_nodes':sum(len(r['labels']) for r in oldplan['extracts'].values()),'new_nodes':sum(len(r['labels']) for r in plan['extracts'].values()),'new_nodes_added':len(newlabels),'new_written_proofs_added':15,'actual_native_binding_query_exit':evidence['new_query']['exit_code']},indent=2))
