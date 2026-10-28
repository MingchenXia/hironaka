from pathlib import Path
import argparse, json, hashlib, collections

p=argparse.ArgumentParser()
p.add_argument('old')
p.add_argument('native')
p.add_argument('output')
p.add_argument('--allowed-native-extra',action='append',default=[])
a=p.parse_args()

ARITIES={
 'bvar':(1,0),'fvar':(1,0),'mvar':(1,0),'sort':(1,0),
 'constant':(2,0),'application':(0,2),'lambda':(2,2),'forall':(2,2),
 'let':(2,3),'naturalLiteral':(1,0),'stringLiteral':(1,0),
 'metadata':(1,1),'projection':(2,1),
}
def load(path):
 result={}
 for line in Path(path).open():
  r=json.loads(line)
  key=(r['module'],r['name'])
  assert key not in result,('duplicate actual constant',key)
  nodes=r['fullExprNodes']
  for i,n in enumerate(nodes):
   assert set(n)=={'tag','data','children'}
   assert n['tag'] in ARITIES,('unknown Expr constructor',key,n)
   d,c=ARITIES[n['tag']]
   assert len(n['data'])==d and len(n['children'])==c
   assert all(type(k) is int and 0<=k<i for k in n['children']),('invalid/cyclic child',key,i)
  roots=[r['typeRoot']]+([] if r['valueRoot'] is None else [r['valueRoot']])
  assert all(type(k) is int and 0<=k<len(nodes) for k in roots)
  reachable=set();pending=roots[:]
  while pending:
   k=pending.pop()
   if k in reachable:continue
   reachable.add(k);pending.extend(nodes[k]['children'])
  assert reachable==set(range(len(nodes))),('unreachable or missing nodes',key)
  if r['kind'] in ['definition','theorem','opaque']:
   assert r['valueRoot'] is not None,('missing complete actual body',key)
  result[key]=r
 return result

def equal_nodes(x,y,rx,ry):
 if rx is None or ry is None:return (rx is ry,None)
 pending=[(rx,ry)];seen=set()
 while pending:
  i,j=pending.pop()
  if (i,j) in seen:continue
  seen.add((i,j));nx=x[i];ny=y[j]
  if nx['tag']!=ny['tag'] or nx['data']!=ny['data'] or len(nx['children'])!=len(ny['children']):
   return False,{'old_node':i,'native_node':j,'old':nx,'native':ny}
  pending.extend(zip(nx['children'],ny['children']))
 return True,None

old=load(a.old);native=load(a.native)
missing=sorted(set(old)-set(native));extra=sorted(set(native)-set(old))
allowed=set(a.allowed_native_extra)
unapproved=[k for k in extra if k[1] not in allowed]
assert allowed=={k[1] for k in extra if k[1] in allowed},'Unused or misspelled allowed extra name'
bad=[];counts=collections.defaultdict(lambda:{'constants':0,'types_exact':0,'values_exact':0,'theorems':0,'theorem_proofs_exact':0})
for key in sorted(set(old)&set(native)):
 x,y=old[key],native[key];c=counts[key[0]];c['constants']+=1
 for field in ['exact_name_tree','kind','levelParams']:
  if x[field]!=y[field]:bad.append({'constant':key,'field':field,'old':x[field],'native':y[field]})
 ok,diff=equal_nodes(x['fullExprNodes'],y['fullExprNodes'],x['typeRoot'],y['typeRoot'])
 if ok:c['types_exact']+=1
 else:bad.append({'constant':key,'field':'type','difference':diff})
 ok,diff=equal_nodes(x['fullExprNodes'],y['fullExprNodes'],x['valueRoot'],y['valueRoot'])
 if ok:c['values_exact']+=1
 else:bad.append({'constant':key,'field':'whole_value','difference':diff})
 if x['kind']=='theorem':
  c['theorems']+=1
  if ok:c['theorem_proofs_exact']+=1

sha=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
report={'status':'EXACT_ALL_FULL_EXPR_DAG_MATCH' if not missing and not unapproved and not bad else 'BLOCKED_EXACT_DIFFERENCE',
 'old':{'path':a.old,'sha256':sha(a.old),'all_actual_constants':len(old)},
 'native':{'path':a.native,'sha256':sha(a.native),'all_actual_constants':len(native)},
 'comparator':{'path':str(Path(__file__).resolve()),'sha256':sha(__file__)},
 'module_counts':dict(counts),'missing':missing,'native_extras':extra,
 'approved_native_extras':sorted(allowed),'unapproved_native_extras':unapproved,'differences':bad,
 'fallbacks':0,'auxiliaries_skipped':0,'proof_numbers_erased':0,'binder_names_erased':0,
 'defeq_or_alpha_comparison':False,'metadata_preserved_in_full':True,
 'method':'Full structural Expr DAG constructor/field/child comparison; all Name/Level/DataValue/Syntax fields retained; no hash used to decide equality'}
Path(a.output).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['differences','module_counts']},ensure_ascii=False))
if missing or unapproved or bad:raise SystemExit(1)
