"""Restore only the two explicit, original declaration elaboration contexts.

Every accepted replacement is guarded by complete before/after file hashes.
The original declaration statements and bodies are retained without changes.
"""
from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parents[1]
for repair in json.loads((r/'scripts/upstream_original_context_repairs.json').read_text()):
 p=r/(repair['protected_module'].replace('.','/')+'.lean');s=p.read_text();h=hashlib.sha256(s.encode()).hexdigest()
 if h==repair['after_sha256']:continue
 assert h==repair['prior_sha256'],p
 replacements=repair.get('replacements',[{'before':repair.get('before'),'after':repair.get('after')}])
 out=s
 for change in replacements:
  assert change['before'] and out.count(change['before'])==1,p
  out=out.replace(change['before'],change['after'],1)
 assert hashlib.sha256(out.encode()).hexdigest()==repair['after_sha256'];p.write_text(out)
