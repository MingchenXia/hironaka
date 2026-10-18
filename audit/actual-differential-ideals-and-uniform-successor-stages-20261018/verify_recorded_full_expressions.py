"""Reproduce full comparison of every new actual root from lossless captures."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
COMPARATOR=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
SHA='28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(COMPARATOR.read_bytes())==SHA
manifest={r['path']:r for r in json.loads((HERE/'recorded-full-expression-captures.json').read_text())}
assert set(manifest)=={'native-full-expressions.jsonl','public-full-expressions.jsonl'}
with tempfile.TemporaryDirectory(prefix='hironaka346-full-expression-replay-') as directory:
 temp=Path(directory)
 for name,rec in manifest.items():
  source=HERE/rec['gzip_path'];assert sha(source.read_bytes())==rec['gzip_sha256']
  h=hashlib.sha256();size=0
  with gzip.open(source,'rb') as src,(temp/name).open('wb') as dst:
   for block in iter(lambda:src.read(1024*1024),b''):h.update(block);size+=len(block);dst.write(block)
  assert h.hexdigest()==rec['sha256'] and size==rec['bytes']
 out=temp/'full-comparison.json'
 subprocess.run([sys.executable,str(COMPARATOR),str(temp/'native-full-expressions.jsonl'),
  str(temp/'public-full-expressions.jsonl'),str(out)],cwd=ROOT,check=True)
 report=json.loads(out.read_text())
 assert report['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
 assert report['old']['all_actual_constants']==report['native']['all_actual_constants']==108
 assert sum(r['theorems'] for r in report['module_counts'].values())==66
 assert not report['differences'] and not report['missing'] and not report['native_extras']
 assert report['fallbacks']==report['auxiliaries_skipped']==report['proof_numbers_erased']==report['binder_names_erased']==0
 assert not report['defeq_or_alpha_comparison'] and report['metadata_preserved_in_full']
print('PASS_ALL_108_RECORDED_ACTUAL_ROOTS_AND_66_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON')
