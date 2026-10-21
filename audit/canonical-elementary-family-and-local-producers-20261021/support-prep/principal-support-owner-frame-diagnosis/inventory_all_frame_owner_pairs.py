from pathlib import Path
import gzip,json,collections,hashlib
A=Path('/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021');W=A/'support-prep/principal-support-owner-frame-diagnosis'
# Reuse only the literal Name parser/observed-frame readers; no prior script top-level execution.
import ast
s=ast.parse((W/'inspect_all_raw_branches.py').read_text());e={};exec(compile(ast.Module(body=[n for n in s.body if isinstance(n,ast.FunctionDef) and n.name in ['parts']],type_ignores=[]),'literal-name-reader','exec'),e);parts=e['parts']
def anyframes(cs):
 starts=[]
 for i,c in enumerate(cs):
  if c==('str','_@'):
   starts.append(i+1)
   if cs[i+1:i+3]==[('str','_internal'),('num',0)]:starts.append(i+3)
  if c==('str','_hygCtx') and i+1<len(cs) and cs[i+1][0]=='num' and ('str','_@') in cs[:i]:starts.append(i+2)
 out=[]
 for start in starts:
  end=start
  while end<len(cs) and cs[end][0]=='str':end+=1
  if end>start and end+1<len(cs) and cs[end][0]=='num' and cs[end+1]==('str','_hygCtx'):
   out.append({'start':start,'end':end,'owner':'.'.join(c[1] for c in cs[start:end]),'scope_seed':cs[end][1],'suffix':cs[end:]})
 return out
subjects=[('CoefficientRestrictionSupportOriginalExact','CoefficientIdealRestriction'),('CoefficientRestrictionTowerIffOriginalExact','CoefficientRestrictionTower'),('NormalDerivativeChartIdealOriginalExact','NormalDerivativeChart')];out=[]
for short,parent in subjects:
 mod='Hironaka.Support.'+short;d=A/'final-per-module-expressions'/mod/'attempt1'
 def read(file):
  with gzip.open(d/file,'rt') as f:return {r['name']:r for r in map(json.loads,f)}
 old=read('original-unfiltered.jsonl.gz');pub=read('public-unfiltered.jsonl.gz');pairs={}
 for name,y in pub.items():
  x=old[name]
  for field in ['typeRoot','valueRoot']:
   if x[field] is None:continue
   todo=[(x[field],y[field])];seen=set()
   while todo:
    i,j=todo.pop()
    if (i,j) in seen:continue
    seen.add((i,j));u=x['fullExprNodes'][i];v=y['fullExprNodes'][j];todo.extend(zip(u['children'],v['children']))
    def names(a,b):
     ac=parts(a);bc=parts(b)
     if ac is not None and bc is not None:
      af=anyframes(ac);bf=anyframes(bc)
      assert len(af)==len(bf),(mod,name,field,i,j)
      for aa,bb in zip(af,bf):
       k=(aa['owner'],bb['owner']);row=pairs.setdefault(k,{'observed_original_frame':aa['owner'],'observed_public_frame':bb['owner'],'scope_seeds':set(),'occurrences':0,'examples':[]})
       assert aa['scope_seed']==bb['scope_seed'];row['scope_seeds'].add(aa['scope_seed']);row['occurrences']+=1
       if len(row['examples'])<3:row['examples'].append({'root':name,'field':field,'old_node':i,'public_node':j,'old_raw_name_tree':a,'public_raw_name_tree':b})
      return
     if type(a) is list and type(b) is list:
      for q,r in zip(a,b):names(q,r)
     elif type(a) is dict and type(b) is dict:
      for k in set(a)&set(b):names(a[k],b[k])
    names(u['data'],v['data'])
 for p in pairs.values():p['scope_seeds']=sorted(p['scope_seeds'])
 out.append({'module':mod,'observed_all_frame_owner_pairs':list(pairs.values()),'required_own_corrected_original_capture_input_pair':{'source_parent':'TranscendentalNakamaye.Pending.'+parent,'actual_new_public_owner':mod},'additional_differing_inherited_frame_owner_pairs':[r for r in pairs.values() if r['observed_original_frame']!=r['observed_public_frame'] and r['observed_public_frame']!=mod],'already_equal_foreign_or_inherited_frames_do_not_change':[r for r in pairs.values() if r['observed_original_frame']==r['observed_public_frame']]})
receipt={'status':'READ_ONLY_ALL_OBSERVED_OWNER_FRAME_PAIRS_FROM_UNCHANGED_RAW_DAGS','modules':out,'no_frame_or_DAG_rewriting':True,'source_runtime_export_and_formal_gate_changes':False,'normal_derivative_foreign_helper_warning':'Existing ORIGINAL raw rows for FlatChart.nd.eq_1 and FlatChart.psi.eq_1 already match unchanged OLD-owner frames. Any corrected whole-parent own-frame capture must retain a truthful separately covered original-OLD helper witness; do not blindly retarget these helper roots or replace raw Name data.'}
f=W/'all-actual-frame-owner-input-pairs.json';f.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
for r in out:print(json.dumps({'module':r['module'],'all_pairs':[(p['observed_original_frame'],p['observed_public_frame'],p['scope_seeds']) for p in r['observed_all_frame_owner_pairs']],'additional_inherited_differing_pairs':len(r['additional_differing_inherited_frame_owner_pairs'])},ensure_ascii=False))
print('SHA',hashlib.sha256(f.read_bytes()).hexdigest())
