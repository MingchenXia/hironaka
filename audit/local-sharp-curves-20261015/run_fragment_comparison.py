"""Run the exact full-body serializer with native and standalone library paths."""
import argparse,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("native_library",type=Path);a=p.parse_args()
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent
e=os.environ.copy();e["LEAN_PATH"]=str(a.native_library)+os.pathsep+e.get("LEAN_PATH", "")
subprocess.run([str(r/".lake/standalone-audit/canonical-fragments"),str(d/"fragment-old-modules.tsv"),str(d/"fragment-new-modules.tsv"),str(d/"fragment-exact-module-renames.tsv"),str(r/".lake/standalone-audit/fragment-original-full.jsonl"),str(r/".lake/standalone-audit/fragment-standalone-full.jsonl"),str(d/"fragment-actual-private-pairs.json")],env=e,cwd=r,check=True)
