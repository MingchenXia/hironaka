#!/usr/bin/env python3
"""Fair <=4-target writer batches, NEW exported mathematical modules only."""
from pathlib import Path
import argparse,ast,hashlib,json,os,re,shutil,subprocess,time
A=Path(__file__).resolve().parent;D=A.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--attempt',default='build-attempt01')
parser.add_argument('--only',action='append',default=[]);args=parser.parse_args()
plan=json.loads((A/'plan.json').read_text())
scope={'re':re};nodes=[x for x in ast.parse((A/'sync_cohort.py').read_text()).body
 if isinstance(x,ast.FunctionDef)and x.name in ['uncomment','imports']]
exec(compile(ast.Module(body=nodes,type_ignores=[]),'cohort-import-parser','exec'),scope)
rows=plan['source_modules']+plan['support_extracts'];by={r['destination_module']:r for r in rows}
ordered=[];seen=set();active=set()
def visit(m):
 if m in seen:return
 assert m not in active,('New import cycle',m);active.add(m)
 for x in scope['imports']((D/by[m]['destination_path']).read_text()):
  if x in by:visit(x)
 active.remove(m);seen.add(m);ordered.append(m)
for m in by:visit(m)
assert len(ordered)==len(rows)
if args.only:
 assert set(args.only)<=set(ordered)
 ordered=[m for m in ordered if m in args.only]
out=A/args.attempt;out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs={r['destination_path']:sha(D/r['destination_path'])for r in rows}
(out/'source-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
state={'status':'RUNNING','native_pin':plan['native_revision'],'new_modules':len(rows),
 'ordered_modules':ordered,'maximum_targets_per_batch':4,'results':[],
 'source_inputs_sha256':sha(out/'source-inputs.json'),'all_children_reaped':False}
def save(): (out/'verification.json').write_text(json.dumps(state,indent=2)+'\n')
save();env=dict(os.environ,LEAN_NUM_THREADS='1')
for i in range(0,len(ordered),4):
 free=shutil.disk_usage(D).free
 if free<2*1024**3:
  state['status']='PAUSED_DISK_BELOW_2_GIB';save();raise SystemExit(2)
 batch=ordered[i:i+4];folder=out/f'batch-{i//4+1:02d}';folder.mkdir()
 cmd=['flock','/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock',
      'lake','--no-cache','--wfail','build',*['+'+m+':olean'for m in batch]]
 start=time.monotonic()
 with(folder/'build.log').open('w')as log:
  p=subprocess.run(cmd,cwd=D,env=env,stdout=log,stderr=subprocess.STDOUT)
 (folder/'build.exit').write_text(str(p.returncode)+'\n')
 text=(folder/'build.log').read_text()
 result={'targets':batch,'command':cmd,'exit':p.returncode,
  'seconds':round(time.monotonic()-start,3),'all_children_reaped':True,
  'log_sha256':sha(folder/'build.log'),
  'warnings':[l for l in text.splitlines()if 'warning:'in l],
  'reported_jobs':re.findall(r'completed successfully \((\d+) jobs\)',text),
  'compiled_target_lines':[l for l in text.splitlines()if 'Built 'in l or 'Replayed 'in l]}
 state['results'].append(result);save()
 print(f'NEW_BATCH {i//4+1}/8 exit={p.returncode} seconds={result["seconds"]}',flush=True)
 if p.returncode:
  state['status']='FAILED_NEW_TARGET_BUILD';state['all_children_reaped']=True;save();raise SystemExit(p.returncode)
 # Release the shared writer between every completed batch.
 time.sleep(.3)
assert inputs=={r['destination_path']:sha(D/r['destination_path'])for r in rows}
state['status']='PASS_REQUIRED_NEW_TARGETS';state['all_children_reaped']=True
state['source_inputs_unchanged']=True
state['artifacts']={m:{'path':'.lake/build/lib/lean/'+m.replace('.','/')+'.olean',
 'sha256':sha(D/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean'))}for m in by}
save();print('REQUIRED_NEW_TARGET_BUILD_PASS',flush=True)
