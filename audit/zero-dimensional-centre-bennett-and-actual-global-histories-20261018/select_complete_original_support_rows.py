"""Select original parent rows verbatim for EVERY actual public support root."""
from pathlib import Path
import hashlib,json
A=Path(__file__).resolve().parent
native=A/'fragment-native-full-expressions.jsonl';public=A/'fragment-public-full-expressions.jsonl';out=A/'fragment-original-selected-for-all-public-roots.jsonl'
key=lambda r:(r['module'],r['name'])
rows={}
counts={}
for line in native.open():
 r=json.loads(line);k=key(r);assert k not in rows;rows[k]=line
 counts[r['module']]=counts.get(r['module'],0)+1
actual=[]
for line in public.open():
 r=json.loads(line);actual.append(key(r))
assert len(actual)==len(set(actual))
missing=[k for k in actual if k not in rows]
assert not missing,missing
out.write_text(''.join(rows[k] for k in actual))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt={'status':'PASS_ORIGINAL_ROWS_SELECTED_FOR_ENTIRE_ACTUAL_PUBLIC_SUPPORT_INVENTORY','full_native_parent_capture_sha256':sha(native),'full_native_parent_actual_roots':len(rows),'full_native_parent_root_counts':counts,'full_unfiltered_public_actual_roots':len(actual),'full_public_capture_sha256':sha(public),'selected_original_rows_sha256':sha(out),'all_actual_public_roots_selected':True,'public_roots_filtered':False,'selected_original_rows_modified':False,'unfiltered_parent_capture_retained':True,'comparison_status':'PENDING_UNCHANGED_COMPARATOR'}
(A/'original-support-selection.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
