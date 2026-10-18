"""Replay every new actual type/value from lossless captures with the unchanged comparator."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
COMPARATOR=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
SHA='28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
assert sha(COMPARATOR.read_bytes())==SHA
manifest={r['path']:r for r in json.loads((HERE/'recorded-full-expression-captures.json').read_text())}
with tempfile.TemporaryDirectory(prefix='hironaka313-full-expression-replay-') as td:
 temp=Path(td)
 needed=['native-full-expressions.jsonl','public-full-expressions.jsonl','fragment-native-full-expressions.jsonl','fragment-public-full-expressions.jsonl','fragment-native-parent-all-actual-full-expressions.jsonl']
 for name in needed:
  rec=manifest[name];compressed=HERE/rec['gzip_path'];assert sha(compressed.read_bytes())==rec['gzip_sha256']
  h=hashlib.sha256();size=0
  with gzip.open(compressed,'rb') as src,(temp/name).open('wb') as dst:
   for part in iter(lambda:src.read(1024*1024),b''):h.update(part);size+=len(part);dst.write(part)
  assert h.hexdigest()==rec['sha256'] and size==rec['bytes'],name
 public=[json.loads(l) for l in (temp/'fragment-public-full-expressions.jsonl').open()]
 keys={(r['module'],r['name']) for r in public};assert len(keys)==len(public)==3
 selected=[l for l in (temp/'fragment-native-parent-all-actual-full-expressions.jsonl').open() if (lambda r:(r['module'],r['name']) in keys)(json.loads(l))]
 assert ''.join(selected).encode()==(temp/'fragment-native-full-expressions.jsonl').read_bytes()
 counts=[];proofs=0
 for stem,expected in [('whole-module',289),('fragment',3)]:
  old='native-full-expressions.jsonl' if stem=='whole-module' else 'fragment-native-full-expressions.jsonl'
  new='public-full-expressions.jsonl' if stem=='whole-module' else 'fragment-public-full-expressions.jsonl'
  out=temp/(stem+'-comparison.json')
  subprocess.run([sys.executable,str(COMPARATOR),str(temp/old),str(temp/new),str(out)],cwd=ROOT,check=True)
  r=json.loads(out.read_text());assert r['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
  assert r['old']['all_actual_constants']==r['native']['all_actual_constants']==expected
  assert not r['differences'] and not r['missing'] and not r['native_extras']
  assert r['fallbacks']==r['auxiliaries_skipped']==r['proof_numbers_erased']==r['binder_names_erased']==0
  assert not r['defeq_or_alpha_comparison'] and r['metadata_preserved_in_full']
  counts.append(expected);proofs+=sum(v['theorems'] for v in r['module_counts'].values())
 assert sum(counts)==292 and proofs==241
print('PASS_ALL_292_RECORDED_ACTUAL_ROOTS_AND_241_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON')
