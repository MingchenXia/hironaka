"""Retain every unfiltered final ALL capture losslessly with deterministic gzip."""
from pathlib import Path
import gzip,hashlib,json
A=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for name in ['native-full-expressions.jsonl','public-full-expressions.jsonl','fragment-native-full-expressions.jsonl','fragment-public-full-expressions.jsonl','fragment-original-selected-for-all-public-roots.jsonl']:
 p=A/name;raw=p.read_bytes();out=A/(name+'.gz')
 with gzip.GzipFile(str(out),'wb',mtime=0) as f:f.write(raw)
 assert gzip.decompress(out.read_bytes())==raw
 rows.append({'original_path':name,'retained_gzip_path':out.name,'uncompressed_sha256':sha(raw),'gzip_sha256':sha(out.read_bytes()),'uncompressed_bytes':len(raw),'actual_root_rows':len(raw.splitlines()),'lossless':True})
(A/'retained-final-expression-captures.json').write_text(json.dumps({'status':'PASS_LOSSLESS_ALL_UNFILTERED_CAPTURE_RETENTION','strict_final_gate_sha256':sha((A/'strict-all-final-comparison.json').read_bytes()),'captures':rows},indent=2)+'\n')
print(json.dumps(rows))
