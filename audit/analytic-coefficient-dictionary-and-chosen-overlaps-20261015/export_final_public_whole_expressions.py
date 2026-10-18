"""Export the final59 public whole modules; reuse the immutable original924-root capture."""
from pathlib import Path
import hashlib,os,subprocess
p=Path(__file__).resolve().parent;r=p.parents[1]
f=r/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
assert hashlib.sha256(f.read_bytes()).hexdigest()=='1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755'
assert hashlib.sha256((p/'native-full-expressions.jsonl').read_bytes()).hexdigest()=='a422643e83772ac49cd2e253207ed8ec3ae0d86d5a93645e2b4179e63ceb1bfc'
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip()
args=[str(p/f) for f in ['public-only-old-modules.tsv','new-modules.tsv','exact-module-renames.tsv','public-only-unused-empty-native.jsonl','public-full-expressions-final.jsonl','public-only-private-pairs.json']]
subprocess.run(['/tmp/hironaka-canonical-scoped-v3',*args],cwd=r,env=env,check=True)
