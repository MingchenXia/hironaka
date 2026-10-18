from pathlib import Path
import os,subprocess
p=Path(__file__).resolve().parent;r=p.parents[1]
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip()
args=[str(p/f) for f in ['unit-ideal-empty-old.tsv','unit-ideal-new.tsv','fragment-exact-module-renames.tsv','unit-ideal-unused-empty-native.jsonl','unit-ideal-restored-public.jsonl','unit-ideal-private-pairs.json']]
subprocess.run(['/tmp/hironaka-canonical-fragments-v2',*args],cwd=r,env=env,check=True)
subprocess.run(['python3',str(r/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'),str(p/'unit-ideal-native-original.jsonl'),str(p/'unit-ideal-restored-public.jsonl'),str(p/'unit-ideal-original-section-context-comparison.json')],cwd=r,check=True)
