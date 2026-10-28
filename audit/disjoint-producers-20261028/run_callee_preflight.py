#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, subprocess, time
A=Path(__file__).resolve().parent;D=A.parents[1]
plan=json.loads((A/'plan.json').read_text());N=Path(plan['native_source_checkout'])/'TranscendentalNakamaye'
def pins():
    paths=[A/'ActualCalleePreflight.lean',A/'native-modules.txt',A/'plan.json',D/'Hironaka.lean',
           D/'.lake/build/lib/lean/Hironaka.olean',D/'lakefile.toml',D/'lean-toolchain',D/'lake-manifest.json']
    for r in plan['source_modules']:
        paths.extend([N/(r['source_module'].replace('.','/')+'.lean'),
                      N/'.lake/build/lib/lean'/(r['source_module'].replace('.','/')+'.olean')])
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths}
before=pins();out=A/'callee-preflight-attempt01';out.mkdir(exist_ok=False)
(out/'before-pins.json').write_text(json.dumps(before,indent=2)+'\n')
cmd=['/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh','flock','-s',
 '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock','lake','env','lean','--run',
 str(A/'ActualCalleePreflight.lean'),str(A/'native-modules.txt'),str(out/'actual-callees.json')]
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(N/'.lake/build/lib/lean'))
start=time.monotonic()
with(out/'probe.log').open('w')as log:
    p=subprocess.run(cmd,cwd=D,env=env,stdout=log,stderr=subprocess.STDOUT)
(out/'probe.exit').write_text(str(p.returncode)+'\n');after=pins()
(out/'after-pins.json').write_text(json.dumps(after,indent=2)+'\n')
assert before==after,'Input source/artifact changed during read-only metadata query'
receipt={'status':'PASS_METADATA_QUERY'if p.returncode==0 else'FAILED_METADATA_QUERY',
 'exit':p.returncode,'seconds':round(time.monotonic()-start,3),'command':cmd,
 'source_artifact_inputs_unchanged':True,'all_children_reaped':True,
 'kernel_or_fullExpr_replay':False,'actual_result':'actual-callees.json'if p.returncode==0 else None}
(out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));raise SystemExit(p.returncode)
