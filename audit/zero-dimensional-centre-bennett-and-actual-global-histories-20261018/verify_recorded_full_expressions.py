"""Reproduce all whole/support strict proof comparisons from lossless retained captures."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys,tempfile
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((A/'retained-final-expression-captures.json').read_text())
assert manifest['status']=='PASS_LOSSLESS_ALL_UNFILTERED_CAPTURE_RETENTION'
strict=json.loads((A/'strict-all-final-comparison.json').read_text())
assert sha((A/'strict-all-final-comparison.json').read_bytes())==manifest['strict_final_gate_sha256']
assert strict['status']=='PASS_ALL_667_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS'
for name,digest in json.loads((A/'strict-frozen-tool-profiles.json').read_text()).items():assert sha((ROOT/name).read_bytes())==digest,name
comparator=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
with tempfile.TemporaryDirectory(prefix='hironaka-major395-entire-captures-') as directory:
 D=Path(directory)
 for item in manifest['captures']:
  packed=(A/item['retained_gzip_path']).read_bytes();assert sha(packed)==item['gzip_sha256'];raw=gzip.decompress(packed)
  assert sha(raw)==item['uncompressed_sha256'] and len(raw)==item['uncompressed_bytes'] and len(raw.splitlines())==item['actual_root_rows'];(D/item['original_path']).write_bytes(raw)
 native={}
 for line in (D/'fragment-native-full-expressions.jsonl').open():
  r=json.loads(line);key=(r['module'],r['name']);assert key not in native;native[key]=line
 actual=[]
 for line in (D/'fragment-public-full-expressions.jsonl').open():
  r=json.loads(line);actual.append((r['module'],r['name']))
 assert len(native)==306 and len(actual)==len(set(actual))==96
 assert ''.join(native[k] for k in actual).encode()==(D/'fragment-original-selected-for-all-public-roots.jsonl').read_bytes()
 reports=[]
 for family,left,right in [('whole','native-full-expressions.jsonl','public-full-expressions.jsonl'),('support','fragment-original-selected-for-all-public-roots.jsonl','fragment-public-full-expressions.jsonl')]:
  out=D/(family+'-comparison.json');subprocess.run([sys.executable,str(comparator),str(D/left),str(D/right),str(out)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
  r=json.loads(out.read_text());assert r['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH' and not r['missing'] and not r['native_extras'] and not r['differences'] and not r['approved_native_extras']
  reports.append(r)
 assert sum(r['old']['all_actual_constants'] for r in reports)==667
 assert sum(sum(c['theorem_proofs_exact'] for c in r['module_counts'].values()) for r in reports)==547
print(json.dumps({'status':'PASS_REPLAY_ALL_667_COMPLETE_RECORDED_TYPES_VALUES_AND_547_PROOFS','all_unfiltered_native_parent_roots':306,'all_actual_public_support_roots':96,'new_root_filters':0,'waivers':0,'frozen_comparator_unchanged':True}))
