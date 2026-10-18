"""Select verbatim original-parent rows for EVERY actual public support root.

The public capture is never filtered. The full original-parent capture remains
available for an independent reviewer and portable reproduction.
"""
from pathlib import Path
import hashlib,json
A=Path(__file__).resolve().parent
raw=A/'fragment-native-full-expressions.jsonl';parent=A/'fragment-native-parent-all-actual-full-expressions.jsonl'
assert not parent.exists(),'Refuse overwriting full parent evidence'
raw.rename(parent)
public=A/'fragment-public-full-expressions.jsonl'
rows=[json.loads(line) for line in public.read_text().splitlines()]
keys={(r['module'],r['name']) for r in rows};assert len(keys)==len(rows)==3
all_lines=parent.read_text().splitlines(keepends=True)
selected=[line for line in all_lines if (lambda r:(r['module'],r['name']) in keys)(json.loads(line))]
assert len(selected)==len(keys)
raw.write_text(''.join(selected))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r={'status':'PASS_ALL_ACTUAL_PUBLIC_SUPPORT_ROOTS_RETAINED_AND_ORIGINAL_PARENT_ROWS_SELECTED_VERBATIM',
 'original_parent_actual_roots':len(all_lines),'public_actual_roots':len(rows),
 'selected_original_roots':len(selected),'outside_selected_original_parent_roots':len(all_lines)-len(selected),
 'public_roots_filtered':0,'selected_original_rows_rewritten':0,
 'original_parent_sha256':sha(parent),'selected_original_sha256':sha(raw),'public_all_sha256':sha(public)}
(A/'fragment-all-public-root-selection.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
