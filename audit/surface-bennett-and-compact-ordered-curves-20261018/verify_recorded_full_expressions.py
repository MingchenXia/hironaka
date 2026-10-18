"""Reproduce all315 complete types, values and279 proofs from retained captures."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys,tempfile
A=Path(__file__).resolve().parent;ROOT=A.parents[1];sha=lambda raw:hashlib.sha256(raw).hexdigest()
manifest=json.loads((A/'retained-final-expression-captures.json').read_text());assert manifest['status']=='PASS_LOSSLESS_ALL_UNFILTERED_CAPTURE_RETENTION'
assert sha((A/'strict-all-final-comparison.json').read_bytes())==manifest['strict_final_gate_sha256']
assert json.loads((A/'strict-all-final-comparison.json').read_text())['status']=='PASS_ALL_315_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS'
for path,h in json.loads((A/'strict-frozen-tool-profiles.json').read_text()).items():assert sha((ROOT/path).read_bytes())==h,path
with tempfile.TemporaryDirectory(prefix='hironaka-major429-entire-captures-')as directory:
 D=Path(directory)
 for r in manifest['captures']:
  packed=(A/r['retained_gzip_path']).read_bytes();assert sha(packed)==r['gzip_sha256'];raw=gzip.decompress(packed)
  assert sha(raw)==r['uncompressed_sha256']and len(raw)==r['uncompressed_bytes']and len(raw.splitlines())==r['actual_root_rows']==315
  (D/r['original_path']).write_bytes(raw)
 out=D/'whole-comparison.json';subprocess.run([sys.executable,str(ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'),str(D/'native-full-expressions.jsonl'),str(D/'public-full-expressions.jsonl'),str(out)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 r=json.loads(out.read_text());assert r['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'and not r['missing']and not r['native_extras']and not r['differences']and not r['approved_native_extras']
 assert r['old']['all_actual_constants']==r['native']['all_actual_constants']==315
 assert sum(c['theorem_proofs_exact']for c in r['module_counts'].values())==279
 assert r['auxiliaries_skipped']==r['proof_numbers_erased']==r['binder_names_erased']==0 and not r['defeq_or_alpha_comparison']
print(json.dumps({'status':'PASS_REPLAY_ALL_315_COMPLETE_RECORDED_TYPES_VALUES_AND_279_PROOFS','new_root_filters':0,'waivers':0,'frozen_comparator_unchanged':True}))
