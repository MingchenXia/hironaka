#!/usr/bin/env python3
"""Exact-module most-private installed-kernel replay of every NEW standalone module.

Uses only completed actual standalone artifacts. No imported-cone --fresh replay,
no old baseline replay and no fingerprints substituted for a kernel invocation.
Resume skips a previous successful invocation only if every recorded actual
kernel part and source file is still byte-identical.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,re
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
P=argparse.ArgumentParser();P.add_argument('--build-pid',type=int,required=True);P.add_argument('--build-log',type=Path);args=P.parse_args()
probe='/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh'
modules=json.loads((A/'provenance.json').read_text());statefile=A/'new-kernel-status.json';logs=A/'new-kernel';logs.mkdir(exist_ok=True)
state=json.loads(statefile.read_text())if statefile.exists()else {'scope':'EXACT316 new whole standalone modules, most-private installed-kernel replay against actual imported environment; no --fresh or old1159 replay','status':'RUNNING','modules':{}}
state['scope']=f'EXACT{len(modules)} new standalone modules (base316 plus genuine complete-original prerequisite extracts), most-private installed-kernel replay; no --fresh or old1159 replay'
state['status']='RUNNING'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def parts(m):
 p=ROOT/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 return [q for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server')]if q.exists()]
def valid(row):
 return row.get('exit_code')==0 and all((ROOT/x['path']).exists()and sha(ROOT/x['path'])==x['sha256']for x in [row['source'],*row['kernel_parts']])
while True:
 pending=[x for x in modules if not valid(state['modules'].get(x['destination_module'],{}))]
 state['passed']=len(modules)-len(pending);state['total']=len(modules)
 if not pending:state['status']=f'PASS_ALL{len(modules)}_NEW_EXACT_KERNEL_REPLAYS';break
 ready=[]
 buildlog=args.build_log.read_text()if args.build_log else'';built=set(re.findall(r'Built (Hironaka[\w.]*) \(',buildlog));fullpass='Build completed successfully'in buildlog
 for row in pending:
  m=row['destination_module'];q=ROOT/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
  if q.exists()and Path(str(q)+'.hash').exists()and(not args.build_log or fullpass or m in built):ready.append(row)
 if not ready:
  live=subprocess.run(['ps','-p',str(args.build_pid),'-o','comm='],capture_output=True,text=True).stdout.strip()=='lake'
  if not live:state['status']='WAITING_MISSING_STANDALONE_BUILD_ARTIFACTS';break
  statefile.write_text(json.dumps(state,indent=2)+'\n');time.sleep(3);continue
 for row in ready:
  m=row['destination_module'];src=ROOT/row['destination_path'];assert sha(src)==row['destination_sha256'],('Source changed',m)
  before=[{'path':str(q.relative_to(ROOT)),'sha256':sha(q),'bytes':q.stat().st_size}for q in parts(m)]
  dest=logs/(m+'.log');cmd=[probe,'lake','env','leanchecker','--verbose',m];start=time.monotonic()
  with dest.open('w')as f:p=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
  assert all(sha(ROOT/x['path'])==x['sha256']for x in before),('Artifact changed during exact replay',m)
  record={'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'source':{'path':row['destination_path'],'sha256':sha(src)},'kernel_parts':before,'command':cmd,'log':str(dest.relative_to(ROOT))}
  state['modules'][m]=record;state['passed']=sum(valid(x)for x in state['modules'].values());statefile.write_text(json.dumps(state,indent=2)+'\n')
  print(json.dumps({'kernel_checked':state['passed'],'total':len(modules),'module':m,'exit_code':p.returncode,'seconds':record['seconds']}),flush=True)
  if p.returncode:state['status']='FAILED_EXACT_KERNEL_REPLAY';statefile.write_text(json.dumps(state,indent=2)+'\n');raise SystemExit(p.returncode)
statefile.write_text(json.dumps(state,indent=2)+'\n');print(state['status'],flush=True)
if state['passed']!=len(modules):raise SystemExit(3)
