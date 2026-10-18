"""Run unmodified ALL capture tools over every actual new module/support root."""
from pathlib import Path
import os, sys, json, hashlib, subprocess
A=Path(__file__).resolve().parent; ROOT=A.parents[1]
NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
snapshot=json.loads((A/'strict-capture-source-and-kernel-snapshot.json').read_text())
def check():
 for r in snapshot:
  for root, key in [(NATIVE,'native'),(ROOT,'public')]:
   module=r[key+'_module']; stem=module.replace('.','/')
   assert sha(root/(stem+'.lean'))==r[key+'_source_sha256'],('source changed',module)
   assert sha(root/'.lake/build/lib/lean'/(stem+'.olean'))==r[key+'_olean_sha256'],('compiled module changed',module)
 for p,h in json.loads((A/'strict-frozen-tool-profiles.json').read_text()).items():
  assert sha(ROOT/p)==h,p
check()
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=':'.join(subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,env=env,text=True).strip() for root in [NATIVE,ROOT])
family=sys.argv[1]
assert family in ['whole','support']
if family=='whole':
 binary='/tmp/hironaka-canonical-scoped-v3'
 files=['old-modules.tsv','new-modules.tsv','exact-module-renames.tsv','native-full-expressions.jsonl','public-full-expressions.jsonl','exact-private-pairs.json']
else:
 binary='/tmp/hironaka-canonical-fragments-v2'
 files=['fragment-old-modules.tsv','fragment-new-modules.tsv','fragment-exact-module-renames.tsv','fragment-native-full-expressions.jsonl','fragment-public-full-expressions.jsonl','fragment-exact-private-pairs.json']
subprocess.run([binary,*[str(A/f) for f in files]],cwd=ROOT,env=env,check=True)
check()
(A/(family+'-strict-capture-input-preservation.json')).write_text(json.dumps({'status':'PASS','all_source_and_olean_inputs_preserved':True,'frozen_tool_profiles_preserved':True,'records':len(snapshot),'family':family},indent=2)+'\n')
