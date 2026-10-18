"""Compare every actual root in all 22 pure original support modules."""
from pathlib import Path
import os,subprocess
here=Path(__file__).resolve().parent;root=here.parents[1]
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
paths=[subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=p,env=env).decode().strip() for p in [Path('/workspace/archon-nakamaye/TranscendentalNakamaye'),root]]
env['LEAN_PATH']=':'.join(paths)
args=[str(here/f) for f in ['fragment-old-modules.tsv','fragment-new-modules.tsv','fragment-exact-module-renames.tsv','fragment-native-full-expressions.jsonl','fragment-public-full-expressions.jsonl','fragment-exact-private-pairs.json']]
subprocess.run(['/tmp/hironaka-canonical-fragments-v2',*args],cwd=root,env=env,check=True)
