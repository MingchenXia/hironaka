import os,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[2];a=Path(__file__).resolve().parent
e=os.environ.copy();e["LEAN_PATH"]="/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/build/lib/lean:"+e.get("LEAN_PATH","")
subprocess.run(["lean","--run",str(a/"FindMissingSupport.lean"),str(a/"combined-old-modules.tsv"),str(a/"existing-public-modules.tsv"),str(r/"audit/controlled-smooth-pullback-20261015/exact-module-renames.tsv"),str(a/"missing-support.json")],cwd=r,env=e,check=True)
