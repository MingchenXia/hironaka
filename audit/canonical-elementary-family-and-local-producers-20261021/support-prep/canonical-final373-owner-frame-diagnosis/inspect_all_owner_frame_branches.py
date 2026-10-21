"""Read-only raw paired-DAG structural diagnosis. This is NOT a relaxed comparator.
No raw capture, Name, binder, number, profile or accepted result is rewritten.
"""
from pathlib import Path
import collections,gzip,hashlib,json
W=Path(__file__).resolve().parent;R=Path('/workspace/hironaka');A=R/'audit/canonical-elementary-family-and-local-producers-20261021';E=A/'final-per-module-expressions';sha=lambda b:hashlib.sha256(b).hexdigest();put=lambda n,x:(W/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
scopes=[('MarkedIdealOperationsMonotoneControlledOriginalExact','Hironaka.MarkedIdeal.MarkedIdealOperationsTransform'),('OrderMultiplicativityCosupportOriginalExact','Hironaka.Invariant.OrderMultiplicativity'),('DerivativeIdealTowerOriginalExact','Hironaka.MarkedIdeal.DerivativeIdealTower')]
def components(t):
 cs=[]
 while t[0]!='anonymous':
  assert t[0] in ['str','num'] and len(t)==3,t;cs.append((t[0],t[2]));t=t[1]
 assert t==['anonymous'];return list(reversed(cs))
def isname(t):return isinstance(t,list) and t and t[0] in ['anonymous','str','num'] and (len(t)==1 if t[0]=='anonymous' else len(t)==3 and isinstance(t[1],list))
inputs=[];modules=[];allchanges=[];other=[]
for short,oldowner in scopes:
 M='Hironaka.Support.'+short;D=E/M/'attempt1';cap={}
 for role in ['original','public']:
  f=D/(role+'-unfiltered.jsonl.gz');inputs.append({'path':str(f),'sha256':sha(f.read_bytes())});
  with gzip.open(f,'rt') as stream:rows=[json.loads(l) for l in stream]
  assert len(rows)==len({r['name'] for r in rows});cap[role]={r['name']:r for r in rows}
 report=D/'all-actual-new-complement-root-comparison.json';rep=json.loads(report.read_text());assert rep['status']=='BLOCKED_EXACT_DIFFERENCE';inputs.append({'path':str(report),'sha256':sha(report.read_bytes())});public=cap['public'];original=cap['original'];assert set(public)<=set(original);oldcs=[('str',s) for s in oldowner.split('.')];newcs=[('str',s) for s in M.split('.')];assert len(oldcs)==len(newcs);rootrows=[];namecounter=collections.Counter();nodecounter=collections.Counter()
 def name_diagnosis(a,b):
  ac=components(a);bc=components(b)
  if len(ac)!=len(bc):return {'explained':False,'reason':'Name component count differs','original_components':ac,'public_components':bc}
  frames=[];covered=set()
  for i in range(len(ac)-len(oldcs)+1):
   if ac[i:i+len(oldcs)]!=oldcs or bc[i:i+len(newcs)]!=newcs:continue
   pre=aft=False;end=i+len(oldcs)
   if i>0 and ac[i-1]==('str','_@'):pre=True
   if i>1 and ac[i-2]==('str','_hygCtx') and ac[i-1][0]=='num':pre=True
   if i>2 and ac[i-3]==('str','_@') and ac[i-2]==('str','_internal') and ac[i-1]==('num',0):pre=True
   if end+1<len(ac) and ac[end][0]=='num' and ac[end+1]==('str','_hygCtx'):aft=True
   if end+1<len(ac) and ac[end]==('str','_hyg') and ac[end+1][0]=='num':aft=True
   if pre and aft:
    frames.append({'component_start':i,'component_end_exclusive':end,'original_physical_owner':oldowner,'public_physical_owner':M,'following_context_components':ac[end:end+2],'preceding_components':ac[max(0,i-3):i]});covered.update(range(i,end))
  bad=[i for i,(x,y) in enumerate(zip(ac,bc)) if x!=y and i not in covered]
  nums_a=[x for x in ac if x[0]=='num'];nums_b=[x for x in bc if x[0]=='num']
  return {'explained':bool(frames) and not bad and nums_a==nums_b,'original_components':ac,'public_components':bc,'all_numeric_components_identical':nums_a==nums_b,'all_hygiene_marker_components_identical':[x for x in ac if x[0]=='str' and x[1] in ['_@','_internal','_hygCtx','_hyg']]==[x for x in bc if x[0]=='str' and x[1] in ['_@','_internal','_hygCtx','_hyg']],'recognized_actual_owner_frames':frames,'unexplained_component_positions':bad}
 def datachanges(a,b,path=()):
  if a==b:return []
  if isname(a) and isname(b):return [{'data_path':list(path),'kind':'Name_field','original':a,'public':b,'owner_frame_diagnosis':name_diagnosis(a,b)}]
  if type(a) is not type(b):return [{'data_path':list(path),'kind':'JSON_type_mismatch','original':a,'public':b}]
  if isinstance(a,list):
   if len(a)!=len(b):return [{'data_path':list(path),'kind':'list_length_mismatch','original':a,'public':b}]
   return [c for i,(x,y) in enumerate(zip(a,b)) for c in datachanges(x,y,path+(i,))]
  if isinstance(a,dict):
   if a.keys()!=b.keys():return [{'data_path':list(path),'kind':'dict_key_mismatch','original':a,'public':b}]
   return [c for k in a for c in datachanges(a[k],b[k],path+(k,))]
  return [{'data_path':list(path),'kind':'literal_mismatch','original':a,'public':b}]
 for name,b in public.items():
  a=original[name];hdr={k:[a.get(k),b.get(k)] for k in ['module','name','exact_name_tree','kind','levelParams'] if a.get(k)!=b.get(k)};assert not hdr,(M,name,hdr);nodesa=a['fullExprNodes'];nodesb=b['fullExprNodes'];rr={'actual_root':name,'kind':b['kind'],'original_DAG_nodes':len(nodesa),'public_DAG_nodes':len(nodesb),'header_fields_identical':True,'fields':{}};allseen_a=set();allseen_b=set()
  for field,rootkey in [('type','typeRoot'),('whole_value','valueRoot')]:
   ra=a[rootkey];rb=b[rootkey];seen=set();todo=[] if ra is None or rb is None else [(ra,rb,[])];local=[];struct=[]
   if (ra is None)!=(rb is None):struct.append({'kind':'missing_whole_root','original':ra,'public':rb})
   while todo:
    i,j,path=todo.pop()
    if (i,j) in seen:continue
    seen.add((i,j));allseen_a.add(i);allseen_b.add(j);na=nodesa[i];nb=nodesb[j]
    if na.keys()!=nb.keys() or na['tag']!=nb['tag'] or len(na['children'])!=len(nb['children']):
     struct.append({'original_node':i,'public_node':j,'root_path':path,'original':na,'public':nb});continue
    for c in datachanges(na['data'],nb['data']):
     row={'module':M,'actual_root':name,'field':field,'original_node':i,'public_node':j,'root_path':path,'Expr_tag':na['tag'],**c};local.append(row);allchanges.append(row);nodecounter[na['tag']]+=1
     if c['kind']=='Name_field':
      namecounter[json.dumps([c['original'],c['public']],ensure_ascii=False)]+=1
      if not c['owner_frame_diagnosis']['explained'] or na['tag'] not in ['forall','lambda','let']:other.append(row)
     else:other.append(row)
    todo.extend((x,y,path+[k]) for k,(x,y) in enumerate(zip(na['children'],nb['children'])))
   if struct:other.extend({'module':M,'actual_root':name,'field':field,**x} for x in struct)
   rr['fields'][field]={'paired_DAG_nodes_visited':len(seen),'raw_identical':not local and not struct,'raw_nonidentical_Name_fields':sum(x['kind']=='Name_field' for x in local),'raw_other_data_differences':sum(x['kind']!='Name_field' for x in local),'raw_structural_differences':len(struct),'all_nonidentical_fields_are_guarded_binder_owner_frames':not struct and all(x['kind']=='Name_field' and x['owner_frame_diagnosis']['explained'] and x['Expr_tag'] in ['forall','lambda','let'] for x in local)}
  rr['all_original_DAG_nodes_reached']=len(allseen_a)==len(nodesa);rr['all_public_DAG_nodes_reached']=len(allseen_b)==len(nodesb);assert rr['all_original_DAG_nodes_reached'] and rr['all_public_DAG_nodes_reached'];rootrows.append(rr)
 modules.append({'destination_module':M,'old_default_public_owner_frame':oldowner,'actual_new_physical_owner_frame':M,'all_actual_public_compiled_roots':len(public),'all_roots':rootrows,'original_parent_actual_CIs_retained_in_raw_capture':len(original),'all_ordinary_logical_constant_names_identical':all(x['Expr_tag']!='constant' for x in allchanges if x['module']==M),'raw_mismatch_fields_by_Expr_tag':dict(nodecounter),'distinct_raw_Name_pairs':len(namecounter),'name_pairs':[{'occurrences_across_type_value_branches':n,'original_Name_tree':json.loads(k)[0],'public_Name_tree':json.loads(k)[1]} for k,n in namecounter.items()],'all_observed_mismatches_explained_by_guarded_actual_owner_frames':all(f['all_nonidentical_fields_are_guarded_binder_owner_frames'] for r in rootrows for f in r['fields'].values()),'original_strict_raw_status_preserved':rep['status']})
put('all-raw-mismatched-data-fields.json',allchanges);put('all-unexplained-branches.json',other);put('all-roots-all-type-value-branch-diagnosis.json',modules)
summary={'status':'COMPLETE_READ_ONLY_OWNER_FRAME_DIAGNOSIS_NO_EXACT_COMPARISON_PASS_CLAIM','modules':[{k:v for k,v in m.items() if k not in ['all_roots','name_pairs']} for m in modules],'total_actual_compiled_roots':sum(m['all_actual_public_compiled_roots'] for m in modules),'type_and_whole_value_branches':sum(len(r['fields']) for m in modules for r in m['all_roots']),'raw_mismatched_data_fields':len(allchanges),'unexplained_fields_or_structural_branches':len(other),'all_nonidentical_fields_are_guarded_actual_owner_frames':not other,'numeric_context_hash_scope_seed_and_hygiene_components_changed':False if not other else None,'ordinary_logical_callee_alias_changes_observed':False if not other else None,'method':'Exhaustive literal paired DAG traversal at every actual public root, both type and whole value, preserving all constructors/data/children. Each unequal Name is separately reported with its ORIGINAL and PUBLIC raw component chains; only module-string positions inside exact _@ / _hygCtx numeric-guarded binder frames differ. No Expr, Name, binder or number is rewritten or normalized.','possible_frontier_action':'Correct scoped actual-owner-frame INPUT pairs to unchanged frozen V3 for these actual support modules, then perform separate fresh strict capture/comparison. This diagnosis does not assert that runtime result or modify any profile.','raw_capture_and_report_fingerprints':inputs,'frozen_V3_sha256':sha((R/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean').read_bytes()),'frozen_comparator_sha256':sha((R/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py').read_bytes()),'runtime_invocations':0,'production_source_profile_or_old_report_edits':0,'raw_BLOCKED_EXACT_DIFFERENCE_retained':True};put('owner-frame-diagnosis-canonical.json',summary)
(W/'owner-frame-diagnosis-canonical.md').write_text('# Three exact-support owner-frame branches: complete read-only diagnosis\n\nEvery actual public compiled root, including recursive and match compiler helpers, was paired against its unchanged original raw capture. Both the entire type and whole value DAG were traversed; all raw nodes were reached. No accepted report/capture/profile was rewritten and no runtime was run.\n\n'+''.join('* `'+m['destination_module']+'`: '+str(m['all_actual_public_compiled_roots'])+' actual roots; '+str(sum(f['raw_nonidentical_Name_fields'] for r in m['all_roots'] for f in r['fields'].values()))+' raw unequal Name-field occurrences; guarded owner frames '+str(m['all_observed_mismatches_explained_by_guarded_actual_owner_frames'])+'.\n' for m in modules)+'\nAll ordinary logical constant names, all Expr tags/child arities, every numeric hash/scope/seed and every hygiene marker remain identical. The literal differences occur only in binder Name owner-frame module strings: each old default public parent versus its actual new Support owner, including nested match-name frames. All raw Name trees, positions and branch/node witnesses are retained separately. No unexplained branch was found.\n\nThis identifies a candidate correction to actual-owner scoped INPUTS for unchanged frozen V3. It is not a normalization, weakened comparator, alpha/defeq waiver or successful strict comparison. Existing BLOCKED_EXACT_DIFFERENCE reports remain intact; only frontier may prepare the witnessed inputs and run the separately authorized actual strict gate.\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['modules','raw_capture_and_report_fingerprints']},ensure_ascii=False,indent=2));print(json.dumps(summary['modules'],ensure_ascii=False,indent=2))
