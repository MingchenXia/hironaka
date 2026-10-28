from pathlib import Path
import json,subprocess,concurrent.futures,time,os
A=Path(__file__).resolve().parent.parent;D=A.parents[1];I=A/'independent';mods=json.loads((I/'modules.json').read_text())
probe='/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh';lock='/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock'
env=dict(os.environ);env['PATH']='/workspace/archon-nakamaye/work/lean-runtime/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
jobs=[]
for i,m in enumerate(mods):
 jobs.append((i,'kernel',m,['lake','env','leanchecker','--verbose',m]))
 jobs.append((i,'physical',m,['lake','env','lean',str(I/f'physical-{i:02d}.lean')]))
def run(job):
 i,kind,m,tail=job;log=I/f'{kind}-{i:02d}.log';receipt=I/f'{kind}-{i:02d}-exit.json';assert not log.exists() and not receipt.exists()
 cmd=[probe,'flock','-s',lock,*tail];start=time.monotonic()
 with log.open('wb') as f:p=subprocess.Popen(cmd,cwd=D,env=env,stdout=f,stderr=subprocess.STDOUT);code=p.wait()
 row={'index':i,'module':m,'kind':kind,'command':cmd,'cwd':str(D),'exit':code,'seconds':time.monotonic()-start,'all_children_reaped':True};receipt.write_text(json.dumps(row,indent=2)+'\n');return row
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 rows=[]
 for f in concurrent.futures.as_completed([ex.submit(run,j) for j in jobs]):
  r=f.result();rows.append(r);print(r['kind'],r['index'],r['exit'],flush=True)
(I/'pair-exits.json').write_text(json.dumps(rows,indent=2)+'\n')
assert len(rows)==2*len(mods) and all(r['exit']==0 for r in rows),'One or more independent gates failed; retain raw outputs'
print('ALL_UNIQUE_PAIRS_PASS',len(mods),flush=True)
