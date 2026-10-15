"""Read actual target callee expressions before any old-public-source change."""
from pathlib import Path
import os,subprocess,json
r=Path('/workspace/hironaka');d=r/'audit/local-sharp-curves-20261015';p=d/'geometry-support'
e=os.environ.copy();e['LEAN_PATH']='/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/build/lib/lean'+os.pathsep+e.get('LEAN_PATH','')
with (p/'28-original-coordinate-callee-serializer.log').open('w') as log:
    subprocess.run([str(r/'.lake/standalone-audit/canonical-standalone-v2'),str(p/'coordinate-eventually-callee-old.tsv'),str(p/'coordinate-eventually-callee-new.tsv'),str(r/'audit/controlled-smooth-pullback-20261015/exact-module-renames.tsv'),str(p/'coordinate-callee-original-module.jsonl'),str(p/'coordinate-callee-standalone-module.jsonl'),str(p/'coordinate-callee-private-pairs.json')],env=e,cwd=r,stdout=log,stderr=subprocess.STDOUT,check=True)
target='Hironaka.HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate'
for kind in ['original','standalone']:
    source=p/f'coordinate-callee-{kind}-module.jsonl'
    selected=[s for s in source.read_text().splitlines() if json.loads(s)['name']==target]
    assert len(selected)==1
    (p/f'coordinate-callee-{kind}-target.jsonl').write_text(selected[0]+'\n')
with (p/'29-original-coordinate-callee-comparator.log').open('w') as log:
    subprocess.run(['python',str(d/'compare_full_expr_dag.py'),str(p/'coordinate-callee-original-target.jsonl'),str(p/'coordinate-callee-standalone-target.jsonl'),str(p/'coordinate-callee-before-repair-comparison.json')],cwd=r,stdout=log,stderr=subprocess.STDOUT)
