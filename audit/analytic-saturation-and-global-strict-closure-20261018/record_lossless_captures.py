"""Keep final and initially rejected complete Expr captures in lossless gzip."""
from pathlib import Path
import gzip,hashlib,json,shutil
A=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=['native-full-expressions.jsonl','public-full-expressions.jsonl',
 'public-full-expressions-initial-before-instance-context.jsonl',
 'fragment-native-parent-all-actual-full-expressions.jsonl',
 'fragment-native-full-expressions.jsonl','fragment-public-full-expressions.jsonl']
records=[]
for name in files:
 path=A/name;compressed=A/(name+'.gz')
 with path.open('rb') as src,compressed.open('wb') as target:
  with gzip.GzipFile(filename='',mode='wb',fileobj=target,mtime=0) as dst:
   shutil.copyfileobj(src,dst,1024*1024)
 h=hashlib.sha256();size=0
 with gzip.open(compressed,'rb') as src:
  for block in iter(lambda:src.read(1024*1024),b''):h.update(block);size+=len(block)
 assert h.hexdigest()==sha(path) and size==path.stat().st_size
 records.append({'path':name,'sha256':sha(path),'bytes':size,
  'gzip_path':compressed.name,'gzip_sha256':sha(compressed),'gzip_bytes':compressed.stat().st_size})
(A/'recorded-full-expression-captures.json').write_text(json.dumps(records,indent=2)+'\n')
print('PASS_ALL_SIX_LOSSLESS_CAPTURES',sum(r['bytes'] for r in records),'RAW_BYTES',sum(r['gzip_bytes'] for r in records),'GZIP_BYTES')
