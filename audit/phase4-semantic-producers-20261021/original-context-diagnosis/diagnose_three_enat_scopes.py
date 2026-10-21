from pathlib import Path
import gzip,json,hashlib
A=Path(__file__).resolve().parent.parent
wanted={'HironakaActualDirectionalPivotNormality':['canonical_directional_quotient_power_of_colons'],'HironakaActualExceptionalInitialGeneration':['component_product','initial_eq_component_span_of_filtered']}
def name(t):
 if t[0]=='anonymous':return''
 if t[0]=='str':return (name(t[1])+'.'if name(t[1])else'')+t[2]
 if t[0]=='num':return name(t[1])+'.'+str(t[2])
 return str(t)
def load(p):
 with gzip.open(p,'rt')as f:return {d['name']:d for d in map(json.loads,f)}
allowed=('IsOrderedRing.toIsOrderedAddMonoid','LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid')
rows=[];all_other=[]
for short,suffixes in wanted.items():
 d=A/'final-per-module-expressions'/('Hironaka.Resolution.'+short)/'attempt1';old=load(d/'original-unfiltered.jsonl.gz');pub=load(d/'public-unfiltered.jsonl.gz')
 for suf in suffixes:
  ks=[n for n in old if n.endswith('.'+suf)];assert len(ks)==1;key=ks[0];o=old[key];p=pub[key];on=o['fullExprNodes'];pn=p['fullExprNodes']
  def head(nodes,i):
   while nodes[i]['tag']=='application':i=nodes[i]['children'][0]
   z=nodes[i];return name(z['data'][0])if z['tag']=='constant'else''
  fields=[]
  for field in ['typeRoot','valueRoot']:
   seen=set();stack=[(o[field],p[field],[])];forks=[];other=[]
   while stack:
    a,b,path=stack.pop()
    if (a,b)in seen:continue
    seen.add((a,b));x=on[a];y=pn[b];ha,hb=head(on,a),head(pn,b)
    if (ha,hb)==allowed:
     forks.append({'old_node':a,'public_node':b,'path':path,'original_ancestor':ha,'public_ancestor':hb});continue
    if x['tag']!=y['tag']or x['data']!=y['data']or len(x['children'])!=len(y['children']):other.append({'old_node':a,'public_node':b,'path':path,'old':x,'public':y});continue
    stack.extend((aa,bb,path+[i])for i,(aa,bb)in enumerate(zip(x['children'],y['children'])))
   fields.append({'field':field,'all_paired_nodes_visited':len(seen),'authentic_ENat_class_ancestor_forks':forks,'other_differences':other});all_other.extend(other)
  rows.append({'actual_CI_name':key,'fields':fields,'whole_raw_original_sha256':hashlib.sha256((d/'original-unfiltered.jsonl.gz').read_bytes()).hexdigest(),'whole_raw_public_sha256':hashlib.sha256((d/'public-unfiltered.jsonl.gz').read_bytes()).hexdigest(),'proposed_source_only_context':'attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in','complete_original_declaration_scope':suf})
report={'status':'ALL_BRANCHES_AUTHENTIC_ENAT_ORDER_ANCESTRY_ONLY'if not all_other else'UNCLASSIFIED_DIFFERENCES','rows':rows,'other_differences_count':len(all_other),'source_proof_or_type_changes':0,'Lean_or_capture_or_comparator_replay':False}
(A/'original-context-diagnosis/three-enat-all-branches.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status']);print([(r['complete_original_declaration_scope'],[(f['field'],len(f['authentic_ENat_class_ancestor_forks']),len(f['other_differences']))for f in r['fields']])for r in rows]);assert not all_other
