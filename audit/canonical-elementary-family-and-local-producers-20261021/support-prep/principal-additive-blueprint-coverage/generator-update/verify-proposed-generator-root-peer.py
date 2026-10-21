from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
R=Path('/workspace/hironaka');A=R/'audit/canonical-elementary-family-and-local-producers-20261021';D=A/'support-prep/principal-additive-blueprint-coverage/generator-update'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as ns
from upstream_blueprint_scope import annotate
ns.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
old=load(D/'before/blueprint_original_node_extracts.py','beforegen');new=load(A/'blueprint_original_node_extracts.py','aftergen')
external=json.loads((R/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((R/'scripts/upstream_blueprint_unbound_bindings.json').read_text());typo=json.loads((R/'scripts/upstream_blueprint_typography.json').read_text())
coverage=json.loads((D.parent/'complete-original-node-integration-plan.json').read_text());wanted=set(coverage['minimal_direct_new_complete_nodes']);added=set();rows=[]
meta=re.compile(r'\\(?:lean|upstreamlean|upstreamunbound)\{[^}]*\}|\\(?:leanok|mixedleanok|upstreamleanok|historicalleanok)\b')
for path,spec in new.PLAN['extracts'].items():
 raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',new.PLAN['native_revision']+':'+spec['source_path']]);assert hashlib.sha256(raw).hexdigest()==spec['source_sha256']
 text=ns.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
 for adj in typo.get(Path(path).name,[]):assert text.count(adj['before'])==1;text=text.replace(adj['before'],adj['after'])
 text=annotate(text,external,unbound);before=old.chapter(path,text);after=new.chapter(path,text)
 assert before==(R/path).read_text() and after.startswith(before)
 assert after==(D/('proposed-'+Path(path).name)).read_text();assert hashlib.sha256(after.encode()).hexdigest()==spec['destination_sha256']
 assert spec['labels'][:len(old.PLAN['extracts'][path]['labels'])]==old.PLAN['extracts'][path]['labels']
 for label in old.PLAN['extracts'][path]['labels']:assert old.block(before,label)==new.block(after,label)
 for item in spec.get('additional_original_node_layout',[]):
  label=item['label'];assert label not in added;added.add(label)
  assert meta.sub('',new.block(ns.rename_text_names(raw.decode()),label))==meta.sub('',new.block(after,label))
  full=new.block(after,label)+item['following_original_text'];assert after.count(full)==1
  context=item.get('context_before','');assert not context or (text.count(context)==1 and context+'\n\n'+full in after)
  core=new.block(text,label);pos=text.index(core);assert text.startswith(item['following_original_text'],pos+len(core))
 rows.append({'path':path,'fixed_source_sha256':spec['source_sha256'],'before_sha256':hashlib.sha256(before.encode()).hexdigest(),'after_sha256':hashlib.sha256(after.encode()).hexdigest(),'old_nodes':len(old.PLAN['extracts'][path]['labels']),'new_nodes':len(spec['labels']),'old_proofs':before.count('\\begin{proof}'),'new_proofs':after.count('\\begin{proof}')})
assert added==wanted and len(added)==19
assert sum(x['old_nodes'] for x in rows)==13 and sum(x['new_nodes'] for x in rows)==32
assert sum(x['new_proofs']-x['old_proofs'] for x in rows)==15
upstream={n for s in new.PLAN['extracts'].values() for n in s['separately_verified_original_bindings']};assert len(upstream)==17
w=json.loads((D/'two-actual-original-support-bindings.json').read_text());assert len(w)==2
for x in w:assert x['actual_physical_CIs_matching_name']==1 and len(x['actual_full_type_repr'])>100 and set(x['transitive_axioms'])<={'propext','Classical.choice','Quot.sound'}
assert (D/'two-native-binding-query.exit').read_text().strip()=='0'
receipt={'status':'PASS_INDEPENDENT_ROOT_STATIC_SOURCE_PEER_EXACT_19_WHOLE_NODES_CONTEXTS_AND_ALL_ORIGINAL_TAILS','generator_sha256':sha(A/'blueprint_original_node_extracts.py'),'plan_sha256':sha(A/'blueprint-original-node-extract-plan.json'),'rows':rows,'additional_complete_original_nodes':19,'additional_complete_written_proofs':15,'all_old13_payloads_and_context_prefix_unchanged':True,'all_eight_original_trailing_paragraphs_retained':True,'all_four_authentic_contexts_retained':True,'upstream_only_name_count':len(upstream),'new_native_bindings_actual_full_type_owner_standard_axioms_witness':True,'production_Bp_Lean_or_old_profiles_modified':False,'runtime_build_kernel_or_Expr_invocations':0}
(D/'semantic-peer-root.json').write_text(json.dumps(receipt,indent=2)+'\n')
(D/'semantic-peer-root.md').write_text('Independent root static source peer PASS. Compared fixed Git parent bytes, unchanged original thirteen-node outputs, all nineteen complete statement/proof cores, eight literal following paragraphs and four authentic contexts. Verified the two bounded actual full-type/owner/standard-axiom witnesses and explicit seventeen-name upstream scope. No production write or runtime replay. Final installed source, binding, kernel and expression gates remain separate.\n')
print(json.dumps(receipt))
