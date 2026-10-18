"""Retain every final unfiltered original/public root losslessly and deterministically."""
from pathlib import Path
import gzip,hashlib,json
A=Path(__file__).resolve().parent;sha=lambda raw:hashlib.sha256(raw).hexdigest()
assert json.loads((A/'strict-all-final-comparison.json').read_text())['status']=='PASS_ALL_315_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS'
rows=[]
for name in ['native-full-expressions.jsonl','public-full-expressions.jsonl']:
 raw=(A/name).read_bytes();out=A/(name+'.gz')
 with out.open('wb')as stream:
  with gzip.GzipFile(filename='',mode='wb',fileobj=stream,mtime=0)as g:g.write(raw)
 assert gzip.decompress(out.read_bytes())==raw
 rows.append({'original_path':name,'retained_gzip_path':out.name,'uncompressed_sha256':sha(raw),'gzip_sha256':sha(out.read_bytes()),'uncompressed_bytes':len(raw),'actual_root_rows':len(raw.splitlines()),'lossless':True})
assert all(r['actual_root_rows']==315 for r in rows)
(A/'retained-final-expression-captures.json').write_text(json.dumps({'status':'PASS_LOSSLESS_ALL_UNFILTERED_CAPTURE_RETENTION','strict_final_gate_sha256':sha((A/'strict-all-final-comparison.json').read_bytes()),'captures':rows},indent=2)+'\n');print(json.dumps(rows))
