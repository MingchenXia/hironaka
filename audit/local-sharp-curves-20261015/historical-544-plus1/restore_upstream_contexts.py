"""Restore only the documented original unused declaration context."""
from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parents[1]
for repair in json.loads((r/'scripts/upstream_original_context_repairs.json').read_text()):
 p=r/(repair['protected_module'].replace('.','/')+'.lean');s=p.read_text();h=hashlib.sha256(s.encode()).hexdigest()
 if h==repair['after_sha256']:continue
 assert h==repair['prior_sha256'] and s.count(repair['before'])==1,p
 out=s.replace(repair['before'],repair['after']);assert hashlib.sha256(out.encode()).hexdigest()==repair['after_sha256'];p.write_text(out)
