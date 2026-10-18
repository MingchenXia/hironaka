"""Export every actual whole-module root with the unchanged frozen V3 serializer."""
from pathlib import Path
import hashlib, os, subprocess
here=Path(__file__).resolve().parent; root=here.parents[1]
source=root/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755'
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
paths=[subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=p,env=env,text=True).strip() for p in [Path('/workspace/archon-nakamaye/TranscendentalNakamaye'),root]]
env['LEAN_PATH']=':'.join(paths)
import json
for rec in json.loads((here/'accepted-native-11-source-records.json').read_text()):
 p=Path('/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/build/lib/lean')/(rec['module'].replace('.','/')+'.olean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==rec['native_sha256'],('Accepted native artifact changed',rec['module'])
args=[str(here/f) for f in ['old-modules.tsv','new-modules.tsv','exact-module-renames.tsv','native-full-expressions.jsonl','public-full-expressions.jsonl','exact-private-pairs.json']]
subprocess.run(['/tmp/hironaka-canonical-scoped-v3',*args],cwd=root,env=env,check=True)
