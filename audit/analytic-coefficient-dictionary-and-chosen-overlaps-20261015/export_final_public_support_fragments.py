"""Freshly export ALL85 actual public support roots under unchanged AllV2."""
from pathlib import Path
import os,subprocess,hashlib
p=Path(__file__).resolve().parent;r=p.parents[1]
assert hashlib.sha256((r/'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean').read_bytes()).hexdigest()=='49aba8c3a923533a210946026b6ac67556c82e79d0c603b10c5b15994cf055ab'
assert hashlib.sha256((p/'fragment-native-full-expressions.jsonl').read_bytes()).hexdigest()=='8e079916532f31251788f898b7ce2b33fce56cd2a33664458dd9b42ad86d37a7'
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip()
args=[str(p/f) for f in ['fragment-public-only-old-modules.tsv','fragment-new-modules.tsv','fragment-exact-module-renames.tsv','fragment-public-only-unused-empty-native.jsonl','fragment-public-full-expressions-final.jsonl','fragment-public-only-private-pairs.json']]
subprocess.run(['/tmp/hironaka-canonical-fragments-v2',*args],cwd=r,env=env,check=True)
