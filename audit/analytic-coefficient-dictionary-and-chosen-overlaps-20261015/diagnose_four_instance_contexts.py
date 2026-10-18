"""Bounded four-module diagnostic using the unchanged frozen V3 exporter/comparator."""
from pathlib import Path
import hashlib,json,os,subprocess
here=Path(__file__).resolve().parent
root=here.parents[1]
modules=['Hironaka.Analytic.RemmertSteinFlat','Hironaka.Analytic.RemmertSteinFlatBadSet',
 'Hironaka.Analytic.RemmertSteinGeneral','Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality']
serializer=root/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
comparator=root/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(serializer)=='1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755'
assert sha(comparator)=='28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
for m in modules:
 source=root/(m.replace('.','/')+'.lean')
 compiled=root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 assert compiled.exists() and compiled.stat().st_mtime>=source.stat().st_mtime,('Build this exact source before exporting',m)
(here/'four-module-empty-old.tsv').write_text('')
(here/'four-module-new.tsv').write_text(''.join(m+'\t'+m+'\n' for m in modules))
with (here/'four-module-native-original-filtered.jsonl').open('w') as out:
 for line in (here/'native-full-expressions.jsonl').open():
  if json.loads(line)['module'] in modules:out.write(line)
env=os.environ.copy()
env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH']
env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,env=env,text=True).strip()
args=[str(here/f) for f in ['four-module-empty-old.tsv','four-module-new.tsv','exact-module-renames.tsv',
 'four-module-unused-empty-native.jsonl','four-module-current-public.jsonl','four-module-private-pairs.json']]
subprocess.run(['/tmp/hironaka-canonical-scoped-v3',*args],cwd=root,env=env,check=True)
subprocess.run(['python',str(comparator),str(here/'four-module-native-original-filtered.jsonl'),
 str(here/'four-module-current-public.jsonl'),str(here/'four-module-instance-comparison.json')],cwd=root,check=True)
