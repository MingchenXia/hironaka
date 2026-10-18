"""Bounded full-root strict audit of the original IsPureDim and open-subset support."""
from pathlib import Path
import hashlib,json,os,subprocess
here=Path(__file__).resolve().parent;root=here.parents[1]
serializer=root/'audit/local-sharp-curves-20261015/CanonicalStandaloneFragmentsV2.lean'
comparator=root/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected_serializer='731b4ee0c1700a7af5cd36d1ec5a288948170d76721a45a8a2a003768525e7d8'
assert sha(serializer)==expected_serializer
assert sha(comparator)=='28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
pairs=[('TranscendentalNakamaye.Pending.AnalyticDimensionBasics','Hironaka.Analytic.GeometricPureDimension'),
       ('TranscendentalNakamaye.Pending.AnalyticSubsetOpens','Hironaka.Support.AnalyticSubsetPresentationsExact')]
(here/'puredim-opens-old.tsv').write_text(''.join(a+'\t'+b+'\n' for a,b in pairs))
(here/'puredim-opens-new.tsv').write_text(''.join(b+'\t'+b+'\n' for a,b in pairs))
rename=(here/'fragment-exact-module-renames.tsv').read_text()
for a,b in pairs:
 lines=rename.splitlines(keepends=True);matches=[l for l in lines if l.startswith(a+'\t')];assert len(matches)==1
 rename=rename.replace(matches[0],a+'\t'+b+'\n')
(here/'puredim-opens-renames.tsv').write_text(rename)
for _,m in pairs:
 source=root/(m.replace('.','/')+'.lean');compiled=root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 assert compiled.stat().st_mtime>=source.stat().st_mtime
config=[str(here/f) for f in ['puredim-opens-old.tsv','puredim-opens-new.tsv','puredim-opens-renames.tsv','puredim-opens-native.jsonl','puredim-opens-public.jsonl','puredim-opens-private-pairs.json']]
env=os.environ.copy();env['PATH']='/workspace/lean-toolchains/lean-4.33.1-linux/bin:'+env['PATH'];env['LEAN_NUM_THREADS']='1'
paths=[subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=p,env=env,text=True).strip() for p in [Path('/workspace/archon-nakamaye/TranscendentalNakamaye'),root]]
env['LEAN_PATH']=':'.join(paths)
subprocess.run(['/tmp/hironaka-canonical-fragments-v2',*config],cwd=root,env=env,check=True)
subprocess.run(['python',str(comparator),str(here/'puredim-opens-native.jsonl'),str(here/'puredim-opens-public.jsonl'),str(here/'puredim-opens-full-expression-comparison.json')],cwd=root,check=True)
