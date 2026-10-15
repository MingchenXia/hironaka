"""Export all actual roots of all 67 new whole public modules using the frozen V3 binary.
The original native snapshot is unchanged; all new actual declarations remain included.
"""
from pathlib import Path
import os,subprocess,hashlib
here=Path(__file__).resolve().parent
root=here.parents[1]
binary=Path('/tmp/hironaka-canonical-scoped-v3')
source=root/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755'
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,env=env).decode().strip()
args=[str(here/f) for f in ['public-only-old-modules.tsv','new-modules.tsv','exact-module-renames.tsv','public-only-empty-native.jsonl','public-full-expressions.jsonl','public-only-private-pairs.json']]
subprocess.run([str(binary),*args],cwd=root,env=env,check=True)
