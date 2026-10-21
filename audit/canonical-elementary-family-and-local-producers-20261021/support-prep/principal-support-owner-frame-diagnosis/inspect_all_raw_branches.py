from pathlib import Path
import collections,gzip,hashlib,json
A=Path('/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021');W=A/'support-prep/principal-support-owner-frame-diagnosis'
subjects=[('CoefficientRestrictionSupportOriginalExact','CoefficientIdealRestriction'),('CoefficientRestrictionTowerIffOriginalExact','CoefficientRestrictionTower'),('NormalDerivativeChartIdealOriginalExact','NormalDerivativeChart')]
sha=lambda b:hashlib.sha256(b).hexdigest()
def parts(n):
 if type(n) is not list or not n:return None
 if n==['anonymous']:return []
 if len(n)==3 and n[0] in ['str','num']:
  parent=parts(n[1])
  if parent is None:return None
  if n[0]=='str' and type(n[2]) is not str:return None
  if n[0]=='num' and type(n[2]) is not int:return None
  return parent+[(n[0],n[2])]
 return None
def frames(cs,owner):
 result=[];width=len(owner)
 for i in range(len(cs)-width+1):
  if cs[i:i+width]!=owner:continue
  suffix=cs[i+width:]
  hygiene=(len(suffix)>=2 and ((suffix[0][0]=='num' and suffix[1]==('str','_hygCtx')) or (suffix[0]==('str','_hyg') and suffix[1][0]=='num')))
  direct=i>=1 and cs[i-1]==('str','_@')
  internal=i>=3 and cs[i-3:i]==[('str','_@'),('str','_internal'),('num',0)]
  nested=i>=2 and cs[i-2][0]=='str' and cs[i-2][1]=='_hygCtx' and cs[i-1][0]=='num' and ('str','_@') in cs[:i-2]
  if hygiene and (direct or internal or nested):result.append(i)
 return result
def raw_frame_only(x,y,oldowner,newowner):
 xs=parts(x);ys=parts(y)
 if xs is None or ys is None or len(xs)!=len(ys):return None
 positions=[i for i in frames(xs,oldowner) if ys[i:i+len(newowner)]==newowner and i in frames(ys,newowner)]
 if not positions:return None
 allowed={j for i in positions for j in range(i,i+len(oldowner))}
 if any(a!=b for j,(a,b) in enumerate(zip(xs,ys)) if j not in allowed):return None
 if any(a[0]=='num' and a!=b for a,b in zip(xs,ys)):return None
 if not any(a!=b for a,b in zip(xs,ys)):return None
 return {'module_context_positions':positions,'all_numeric_components_exact':True,'all_non_owner_components_exact':True,'old_components':xs,'public_components':ys}
def load(path):
 b=gzip.decompress(path.read_bytes());rows=[json.loads(l) for l in b.splitlines()];by={r['name']:r for r in rows};assert len(by)==len(rows)
 return by,{'path':str(path),'gzip_sha256':sha(path.read_bytes()),'lossless_uncompressed_sha256':sha(b),'actual_root_count':len(rows)}
summary=[];allfindings=[]
for short,parent in subjects:
 module='Hironaka.Support.'+short;d=A/'final-per-module-expressions'/module/'attempt1'
 old,oldinfo=load(d/'original-unfiltered.jsonl.gz');public,pubinfo=load(d/'public-unfiltered.jsonl.gz')
 report=json.loads((d/'all-actual-new-complement-root-comparison.json').read_text())
 assert report['old']['all_actual_constants']==len(public) and not report['missing'] and not report['native_extras']
 assert all(n in old for n in public)
 oldowner=[('str',s) for s in ('Hironaka.MarkedIdeal.'+parent).split('.')];newowner=[('str',s) for s in module.split('.')]
 rootrows=[];sameframe=collections.Counter();sameframe_examples={};fieldstats=collections.Counter();mismatchstats=collections.Counter();residuals=[];framevariants={}
 for name,y in sorted(public.items()):
  x=old[name];row={'name':name,'kind':y['kind'],'top_metadata_differences':[],'fields':[]}
  for k in ['module','name','exact_name_tree','kind','levelParams']:
   if x[k]!=y[k]:row['top_metadata_differences'].append({'field':k,'old':x[k],'public':y[k]});residuals.append({'name':name,'field':k,'reason':'top metadata difference'})
  for field in ['typeRoot','valueRoot']:
   if x[field] is None or y[field] is None:
    assert x[field] is y[field];row['fields'].append({'field':field,'both_null':True});fieldstats['both_null']+=1;continue
   an=x['fullExprNodes'];bn=y['fullExprNodes'];todo=[(x[field],y[field],[])];seen=set();findings=[];shape=0
   while todo:
    i,j,path=todo.pop()
    if (i,j) in seen:continue
    seen.add((i,j));u=an[i];v=bn[j]
    if u['tag']!=v['tag'] or len(u['children'])!=len(v['children']):
     finding={'classification':'ADDITIONAL_CONSTRUCTOR_OR_ARITY_DIFFERENCE','old_node':i,'public_node':j,'dag_children_path':path,'old_raw_node':u,'public_raw_node':v};findings.append(finding);shape+=1
    # Always traverse paired children, including below EVERY differing binder datum.
    todo.extend((a,b,path+[k]) for k,(a,b) in enumerate(zip(u['children'],v['children'])))
    def literal(a,b,p):
     ap=parts(a);bp=parts(b)
     if ap is not None and bp is not None:
      if a==b:
       for pos in frames(ap,oldowner):
        key=json.dumps(ap[pos+len(oldowner):],ensure_ascii=False);sameframe[key]+=1;sameframe_examples.setdefault(key,{'name':name,'field':field,'old_node':i,'public_node':j,'data_path':p,'raw_identical_name_tree':a})
       return
      frame=raw_frame_only(a,b,oldowner,newowner)
      item={'classification':'EXACT_ACTUAL_MODULE_HYGIENE_OWNER_FRAME_ONLY' if frame else 'ADDITIONAL_NAME_DIFFERENCE','old_node':i,'public_node':j,'dag_children_path':path,'data_path':p,'expr_tag':u['tag'],'old_raw_name_tree':a,'public_raw_name_tree':b}
      if frame:
       item['frame_evidence']=frame;key=json.dumps([a,b],ensure_ascii=False,separators=(',',':'));framevariants.setdefault(key,{'old_raw_name_tree':a,'public_raw_name_tree':b,'frame_evidence':frame,'occurrences':0})['occurrences']+=1
      findings.append(item);return
     if type(a) is not type(b):findings.append({'classification':'ADDITIONAL_DATA_TYPE_DIFFERENCE','old_node':i,'public_node':j,'dag_children_path':path,'data_path':p,'old_raw_data':a,'public_raw_data':b});return
     if type(a) is list:
      if len(a)!=len(b):findings.append({'classification':'ADDITIONAL_DATA_ARITY_DIFFERENCE','old_node':i,'public_node':j,'dag_children_path':path,'data_path':p,'old_raw_data':a,'public_raw_data':b})
      for k,(aa,bb) in enumerate(zip(a,b)):literal(aa,bb,p+[k])
     elif type(a) is dict:
      if set(a)!=set(b):findings.append({'classification':'ADDITIONAL_DATA_KEY_DIFFERENCE','old_node':i,'public_node':j,'dag_children_path':path,'data_path':p,'old_raw_data':a,'public_raw_data':b})
      for k in set(a)&set(b):literal(a[k],b[k],p+[k])
     elif a!=b:findings.append({'classification':'ADDITIONAL_LITERAL_DIFFERENCE','old_node':i,'public_node':j,'dag_children_path':path,'data_path':p,'old_raw_data':a,'public_raw_data':b})
    literal(u['data'],v['data'],[])
   for f in findings:mismatchstats[f['classification']]+=1
   additional=[f for f in findings if f['classification']!='EXACT_ACTUAL_MODULE_HYGIENE_OWNER_FRAME_ONLY']
   if additional:residuals.append({'name':name,'field':field,'additional_findings':additional})
   row['fields'].append({'field':field,'all_paired_node_branches_visited':len(seen),'comparison_did_not_stop_at_differing_data':True,'local_data_or_shape_findings':findings,'owner_frame_findings':len(findings)-len(additional),'additional_findings':len(additional)})
   fieldstats['fields_scanned']+=1;fieldstats['paired_nodes_visited']+=len(seen);fieldstats['fields_with_owner_frame_findings']+=bool(findings);fieldstats['fields_with_additional_findings']+=bool(additional)
  rootrows.append(row)
 diagnosis={'status':'READ_ONLY_ALL_RAW_BRANCHES_OWNER_FRAME_DIAGNOSIS_NOT_A_FORMAL_EQUALITY_GATE','module':module,'original_native_parent':'TranscendentalNakamaye.Pending.'+parent,'original_export_observed_owner_frame':'Hironaka.MarkedIdeal.'+parent,'actual_public_module_owner_frame':module,'raw_original_capture':oldinfo,'raw_public_capture':pubinfo,'frozen_comparator_report':{'path':str(d/'all-actual-new-complement-root-comparison.json'),'sha256':sha((d/'all-actual-new-complement-root-comparison.json').read_bytes()),'status':report['status'],'reported_first_difference_fields':len(report['differences'])},'all_actual_public_metadata_roots_including_compiler_helpers':len(public),'unselected_original_parent_roots_retained_in_lossless_raw_capture':len(old)-len(public),'all_public_types_and_whole_values_scanned':True,'field_statistics':dict(fieldstats),'all_local_difference_classifications':dict(mismatchstats),'additional_actual_mathematical_difference_findings':residuals,'all_observed_differences_confined_to_owner_frame':not residuals,'same_parent_owner_frames_already_identical_and_must_not_be_broadly_retargeted':[{'raw_suffix_components':json.loads(k),'occurrences':n,'example':sameframe_examples[k]} for k,n in sameframe.items()],'distinct_raw_owner_frame_name_pairs':list(framevariants.values()),'root_and_field_details':rootrows,'raw_DAG_or_Name_or_numeric_or_binder_data_rewritten':False,'normalized_candidate_or_replay_created':False,'runtime_kernel_or_Expr_export_invoked':False,'source_or_production_edits':False,'formal_status_remains_raw_BLOCKED_pending_actual_exporter_owner_frame_capture':True,'method':'Traverse every paired child branch of every actual PUBLIC type and whole value against its original raw parent row, even when a node tag/data differs. Compare literal raw data. Classify a Name difference as owner-frame-only solely when an existing _@/internal/nested-hygiene module frame changes from the observed OLD public parent to the actual NEW support owner, every other raw Name component and all numerical components remain identical. No Name or Expr is transformed and no equality gate is rerun.'}
 file=W/(short+'-all-raw-branches.json');file.write_text(json.dumps(diagnosis,ensure_ascii=False,indent=2)+'\n')
 summary.append({'module':module,'raw_public_roots':len(public),'type_whole_value_fields_scanned':fieldstats['fields_scanned'],'all_node_pairs_visited':fieldstats['paired_nodes_visited'],'owner_frame_local_findings':mismatchstats['EXACT_ACTUAL_MODULE_HYGIENE_OWNER_FRAME_ONLY'],'additional_findings':sum(n for k,n in mismatchstats.items() if k!='EXACT_ACTUAL_MODULE_HYGIENE_OWNER_FRAME_ONLY'),'already_equal_same_parent_frame_variants':len(sameframe),'observed_original_owner_frame':diagnosis['original_export_observed_owner_frame'],'actual_new_owner_frame':module,'diagnosis':file.name,'sha256':sha(file.read_bytes())})
 out={k:v for k,v in summary[-1].items() if k not in ['sha256']};print(json.dumps(out,ensure_ascii=False))
(W/'three-support-all-raw-branches-summary.json').write_text(json.dumps({'status':'READ_ONLY_RAW_STRUCTURAL_DIAGNOSIS_ONLY','modules':summary,'raw_captures_and_reports_preserved':True,'no_DAG_Name_numeric_binder_statement_or_proof_normalization':True,'no_source_edit_or_runtime':True,'not_a_new_full_expression_equality_PASS':True},ensure_ascii=False,indent=2)+'\n')
