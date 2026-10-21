"""Read-only paired full-DAG first structural branches; no equality waiver."""
from pathlib import Path
import gzip,json,hashlib
A=Path(__file__).resolve().parent;R=A.parents[1]
state=json.loads((A/'final-per-module-expressions/status.json').read_text())
parents=['HironakaActualExceptionalFilteredDivision','HironakaActualPointOrderRetainingHS','HironakaActualAxisTaylorRigidity','HironakaActualInitialPivotNormality','HironakaActualPersistentPointConeDerivatives','HironakaActualRelativeNormalizedSaturation']
def name(t):
 if t[0]=='anonymous':return''
 if t[0]=='str':return('.'.join(x for x in[name(t[1]),t[2]]if x))
 if t[0]=='num':return name(t[1])+'.'+str(t[2])
 return str(t)
def load(path):
 with gzip.open(R/path,'rt')as f:return {r['name']:r for r in map(json.loads,f)}
def head(nodes,i):
 n=nodes[i]
 if n['tag']=='constant':return name(n['data'][0])
 if n['tag']=='application':return head(nodes,n['children'][0])
 return n['tag']
def short(nodes,i,depth=4):
 n=nodes[i]
 if depth<=0:return head(nodes,i)
 if n['tag']=='constant':return name(n['data'][0])
 if n['tag']=='application':return '('+short(nodes,n['children'][0],depth-1)+' '+short(nodes,n['children'][1],depth-1)+')'
 return n['tag']+str(n['data'])
results=[]
for stem in parents:
 m='Hironaka.Resolution.'+stem;r=state['modules'][m];old=load(r['captures']['original-unfiltered']['path']);new=load(r['captures']['public-unfiltered']['path']);report=json.loads((R/r['every_actual_new_root_comparison']['report']).read_text())
 targets=r['every_actual_new_root_comparison']['difference_roots']
 for target in targets:
  if target.rsplit('.',1)[-1]in['termR','term𝔪','termP']:continue
  a,b=old[target],new[target];an,bn=a['fullExprNodes'],b['fullExprNodes']
  for field in ['typeRoot','valueRoot']:
   seen=set();out=[]
   def walk(i,j,path):
    if(i,j)in seen:return
    seen.add((i,j));x,y=an[i],bn[j]
    if x['tag']!=y['tag']or x['data']!=y['data']or len(x['children'])!=len(y['children']):
     out.append({'old_node':i,'new_node':j,'old_term':short(an,i,7),'new_term':short(bn,j,7),'ancestor_heads':path[-18:]});return
    for k,(c,d)in enumerate(zip(x['children'],y['children'])):walk(c,d,path+[{'old':head(an,i),'new':head(bn,j),'child':k,'old_node':i,'new_node':j}])
   if a[field]is not None and b[field]is not None:walk(a[field],b[field],[])
   if out:results.append({'module':m,'declaration':target,'field':field,'first_structural_branches':out,'source_and_capture_inputs':r['frozen_inputs'],'raw_report':r['every_actual_new_root_comparison']['report']})
output={'status':'READ_ONLY_ALL_RECORDED_MATH_BRANCHES_NO_WAIVER','results':results,'production_or_runtime_edits':False}
(A/'additive40-first-math-context-diagnosis.json').write_text(json.dumps(output,indent=2)+'\n')
for r in results:
 print(r['module'],r['declaration'],r['field'])
 for d in r['first_structural_branches'][:2]:print(d['old_term'][:180],d['new_term'][:180],json.dumps(d['ancestor_heads'][-9:]))
