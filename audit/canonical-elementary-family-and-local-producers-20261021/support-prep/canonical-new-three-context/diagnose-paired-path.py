import json,gzip,hashlib
from pathlib import Path
A=Path('/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021')
OUT=A/'support-prep/canonical-new-three-context'
def load(p):
 p=Path(p)
 if not p.exists():p=Path(str(p)+'.gz')
 op=gzip.open if p.suffix=='.gz' else open
 with op(p,'rt') as f:return {r['name']:r for line in f if (r:=json.loads(line))}
def name(t):
 if t[0]=='anonymous':return ''
 return (name(t[1])+'.'+str(t[2])).lstrip('.')
def pp(ns,i,depth=0):
 n=ns[i]
 if n['tag']=='constant':return name(n['data'][0])
 if n['tag']=='application':
  args=[];j=i
  while ns[j]['tag']=='application':args.append(ns[j]['children'][1]);j=ns[j]['children'][0]
  h=pp(ns,j,depth+1)
  if depth>=2:return '('+h+' …)'
  return '('+h+' '+' '.join(pp(ns,k,depth+1) for k in reversed(args))+')'
 if n['tag']=='bvar':return '#'+str(n['data'][0])
 return n['tag']+str(n['data'])[:80]
def first(x,y,rx,ry):
 pending=[(rx,ry,[])];seen=set()
 while pending:
  i,j,p=pending.pop()
  if (i,j) in seen:continue
  seen.add((i,j));nx=x[i];ny=y[j]
  if nx['tag']!=ny['tag'] or nx['data']!=ny['data'] or len(nx['children'])!=len(ny['children']):return i,j,p
  pending.extend((a,b,p+[(i,j,k)]) for k,(a,b) in enumerate(zip(nx['children'],ny['children'])))
rows=[]
for suffix in ['ActualHomogeneousInitialTangentDerivatives','ActualInitialCoordinateQuotient','ActualTangentCutLayers']:
 P=A/'final-per-module-expressions'/('Hironaka.Resolution.Hironaka'+suffix)/'attempt1'/'raw-complete-parent-comparison.json'
 r=json.loads(P.read_text());old=load(r['old']['path']);new=load(r['native']['path'])
 for d in r['differences']:
  nm=d['constant'][1];o,n=old[nm],new[nm];root='typeRoot' if d['field']=='type' else 'valueRoot'
  i,j,path=first(o['fullExprNodes'],n['fullExprNodes'],o[root],n[root])
  assert (i,j)==(d['difference']['old_node'],d['difference']['native_node'])
  row={'constant':nm,'report':str(P),'field':d['field'],'old_node':i,'native_node':j,'first_difference_agrees_with_frozen_report':True,'old_leaf':pp(o['fullExprNodes'],i),'native_leaf':pp(n['fullExprNodes'],j),'paired_path_tail':[{'child':k,'old_node':a,'native_node':b,'old':pp(o['fullExprNodes'],a),'native':pp(n['fullExprNodes'],b)} for a,b,k in path[-8:]]}
  rows.append(row)
  print('\nCONSTANT',nm,'\nFIRST',row['old_leaf'],'VS',row['native_leaf'])
  for s in row['paired_path_tail']:print(' child',s['child'],'OLD',s['old'],'\n       NEW',s['native'])
(OUT/'paired-first-dag-paths.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
