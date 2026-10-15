"""Compare only the actual original/copy module; no comparator relaxation."""
from pathlib import Path
import os, subprocess
r=Path('/workspace/hironaka')
d=r/'audit/local-sharp-curves-20261015'
p=d/'geometry-support'
e=os.environ.copy()
e['LEAN_PATH']='/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/build/lib/lean'+os.pathsep+e.get('LEAN_PATH','')
with (p/'43-actual-cstar-prime-serializer.log').open('w') as log:
    subprocess.run([str(r/'.lake/standalone-audit/canonical-standalone-v2'),
        str(p/'prime-cstar-old.tsv'),str(p/'prime-cstar-new.tsv'),
        str(r/'audit/controlled-smooth-pullback-20261015/exact-module-renames.tsv'),
        str(p/'prime-cstar-original.jsonl'),str(p/'prime-cstar-standalone.jsonl'),
        str(p/'prime-cstar-private-pairs.json')],env=e,cwd=r,stdout=log,stderr=subprocess.STDOUT,check=True)
with (p/'44-actual-cstar-prime-comparator.log').open('w') as log:
    subprocess.run(['python',str(d/'compare_full_expr_dag.py'),
        str(p/'prime-cstar-original.jsonl'),str(p/'prime-cstar-standalone.jsonl'),
        str(p/'prime-cstar-comparison.json')],env=e,cwd=r,stdout=log,stderr=subprocess.STDOUT,check=True)
