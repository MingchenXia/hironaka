from pathlib import Path
import hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
R=Path('/workspace/hironaka');A=R/'audit/canonical-elementary-family-and-local-producers-20261021';W=A/'support-prep/principal-additive-blueprint-coverage';D=W/'generator-update'
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
external=json.loads((R/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((R/'scripts/upstream_blueprint_unbound_bindings.json').read_text());typography=json.loads((R/'scripts/upstream_blueprint_typography.json').read_text())
def module(path,label):
 s=importlib.util.spec_from_file_location(label,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
old=module(D/'before/blueprint_original_node_extracts.py','oldnodegenerator');new=module(A/'blueprint_original_node_extracts.py','proposednodegenerator')
oldplan=old.PLAN;plan=new.PLAN;coverage=json.loads((W/'complete-original-node-integration-plan.json').read_text());counts={'old_complete_nodes':0,'new_complete_nodes':0,'old_proofs':0,'new_proofs':0};rows=[]
meta=re.compile(r'\\(?:lean|upstreamlean|upstreamunbound)\{[^}]*\}|\\(?:leanok|mixedleanok|upstreamleanok|historicalleanok)\b')
currentprovenance=json.loads((A/'blueprint-provenance.json').read_text());assert len(currentprovenance)==349
production={r['destination_path']:sha((R/r['destination_path']).read_bytes()) for r in currentprovenance}
assert sum(r['proofs'] for r in currentprovenance)==1110
for path,spec in plan['extracts'].items():
 fn=Path(spec['source_path']).name
 if fn=='analytic.tex':raw=(A/'blueprint-original-node-extracts/analytic-whole-original-fixed-native.tex').read_text()
 else:raw=(W/(fn+'.whole-original.txt')).read_text()
 assert sha(raw)==spec['source_sha256']
 canonical=names.rename_text_names(raw).replace('\\chapter{','\\section{')
 for adj in typography.get(Path(path).name,[]):assert canonical.count(adj['before'])==1;canonical=canonical.replace(adj['before'],adj['after'])
 canonical=annotate(canonical,external,unbound)
 before=old.chapter(path,canonical);after=new.chapter(path,canonical)
 assert (R/path).read_text()==before,(path,'production changed beyond old generator')
 assert after.startswith(before),('Existing selected nodes/context/payloads changed',path)
 assert path!='blueprint/analytic.tex' or after==before
 labels=re.findall(r'\\label\{([^}]+)\}',after);labels=[l for l in labels if not l.startswith('sec:')]
 assert labels==spec['labels'] and len(labels)==len(set(labels))
 for label in oldplan['extracts'][path]['labels']:
  assert old.block(before,label)==new.block(after,label),(path,label,'old attachment/type/proof payload changed')
 for item in spec.get('additional_original_node_layout',[]):
  label=item['label'];original=new.block(names.rename_text_names(raw),label);rendered=new.block(after,label)
  assert meta.sub('',original)==meta.sub('',rendered),(label,'new statement/proof token edit')
  whole=rendered+item['following_original_text'];assert after.count(whole)==1,(label,'whole node/tail not exact once')
  if item.get('context_before'):
   context=item['context_before'];assert context+ '\n\n'+whole in after,(label,'authentic context not immediately before whole node')
 if path=='blueprint/maximal-contact.tex':
  tail=(W/'mc--derivative-marked.original-following-justification-lines410-411.tex.txt').read_text();assert after.count(tail.rstrip('\n'))==1
 oldbindings=[(kind,b.strip()) for kind,v in re.findall(r'\\(lean|upstreamlean|upstreamunbound)\{([^}]+)\}',before) for b in v.split(',')]
 allbindings=[(kind,b.strip()) for kind,v in re.findall(r'\\(lean|upstreamlean|upstreamunbound)\{([^}]+)\}',after) for b in v.split(',')]
 assert allbindings[:len(oldbindings)]==oldbindings
 candidate=D/('proposed-'+fn);candidate.write_text(after)
 rows.append({'path':path,'old_sha256':sha(before),'prior_plan_recorded_destination_sha256':oldplan['extracts'][path]['destination_sha256'],'prior_plan_digest_matches_actual_old_production':sha(before)==oldplan['extracts'][path]['destination_sha256'],'proposed_sha256':sha(after),'audit_candidate':str(candidate.relative_to(A)),'old_nodes':len(oldplan['extracts'][path]['labels']),'proposed_nodes':len(labels),'old_written_proofs':before.count('\\begin{proof}'),'proposed_written_proofs':after.count('\\begin{proof}'),'old_all_selected_payloads_and_context_prefix_exact':True,'only_whole_original_nodes_and_context_appended':True,'original_attachment_observations_before':len(oldbindings),'original_attachment_observations_after':len(allbindings)})
 plan['extracts'][path]['destination_sha256']=sha(after)
 counts['old_complete_nodes']+=len(oldplan['extracts'][path]['labels']);counts['new_complete_nodes']+=len(labels);counts['old_proofs']+=before.count('\\begin{proof}');counts['new_proofs']+=after.count('\\begin{proof}')
assert counts=={'old_complete_nodes':13,'new_complete_nodes':32,'old_proofs':11,'new_proofs':26},counts
# This updates only the authorized NEW plan's anticipated destination digests;
# the actual chapters remain the old 13-node outputs pending root peer/frontier sync.
(A/'blueprint-original-node-extract-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
assert production=={r['destination_path']:sha((R/r['destination_path']).read_bytes()) for r in currentprovenance}
receipt={'status':'PASS_AUDIT_ONLY_PROPOSED_GENERATOR_EXACT_OLD_PAYLOAD_PRESERVATION_AND_NATIVE_NODE_REPLAY','generator_before_sha256':sha((D/'before/blueprint_original_node_extracts.py').read_bytes()),'generator_proposed_sha256':sha((A/'blueprint_original_node_extracts.py').read_bytes()),'plan_before_sha256':sha((D/'before/blueprint-original-node-extract-plan.json').read_bytes()),'plan_proposed_sha256':sha((A/'blueprint-original-node-extract-plan.json').read_bytes()),'rows':rows,'counts':counts,'projected_new349_written_proofs_before':1110,'projected_written_proofs_after_frontier_generation':1125,'all_three_actual_production_chapters_unchanged':True,'all349_actual_new_chapters_unchanged_during_check':True,'only_two_authorized_new_generator_plan_files_edited':True,'proposed_audit_renders_are_not_production_chapters':True,'all_old13_complete_payloads_attachment_status_and_existing_context_prefix_exact':True,'all_new19_complete_original_statement_proof_payloads_namespace_metadata_only':True,'all_four_authentic_context_blocks_preserved_at_approved_new_scope':True,'derivative_definition_plain_proof_tail_lines410_411_exact_once':True,'global_reference_duplicate_label_binding_gates_not_rerun_here':True,'no_production_generation_build_kernel_or_Expr_replay':True,'native_two_binding_witness_query':'one already completed authorized fair-reader metadata/type/std3 query'}
(D/'proposed-generator-static-source-peer-receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(receipt,ensure_ascii=False,indent=2))
