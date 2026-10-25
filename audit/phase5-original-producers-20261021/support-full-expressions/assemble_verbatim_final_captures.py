from pathlib import Path
import json,hashlib
A=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def rows(name):
 result={}
 for line in (A/name).read_bytes().splitlines(keepends=True):
  record=json.loads(line);key=(record['module'],record['name']);assert key not in result;result[key]=line
 return result
old=rows('original-unfiltered-selected.jsonl');public=rows('public-unfiltered-all.jsonl')
old_correction=rows('original-owner-corrected-six.jsonl');new_tangent=rows('tangent-corrected-context-all.jsonl')
assert len(old)==len(public)==16 and len(old_correction)==6 and len(new_tangent)==2
assert old_correction.keys()<=old.keys() and new_tangent.keys()<=public.keys()
assert all(k[0]=='Hironaka.Support.ZeroCoordinateDerivativeUnivExact' for k in old_correction)
assert all(k[0]=='Hironaka.Support.ZeroCoordinateTangentUnivExact' for k in new_tangent)
original_final={k:old_correction.get(k,v) for k,v in old.items()}
public_final={k:new_tangent.get(k,v) for k,v in public.items()}
assert original_final.keys()==public_final.keys()
for name,records in [('original-final-verbatim-selected.jsonl',original_final),('public-final-verbatim-all.jsonl',public_final)]:
 (A/name).write_bytes(b''.join(records.values()))
physical=json.loads((A.parent/'new17physical-ci-axioms.json').read_text())
actual={(r['actual_moduleData_owner'],r['actual_name']) for r in physical['all_physical_root_rows'] if '.Support.ZeroCoordinate' in r['actual_moduleData_owner']}
assert actual==public_final.keys()
proofs={k:json.loads(v)['kind'] for k,v in public_final.items()}
(A/'verbatim-row-reuse.json').write_text(json.dumps({'status':'PASS_ALL16_ACTUAL_NEW_SUPPORT_ROOTS_VERBATIM_ASSEMBLED','all_actual_physical_public_roots_retained':True,'actual_roots':16,'actual_theorems':sum(v=='theorem' for v in proofs.values()),'old_exact_rows_reused_verbatim':10,'old_necessary_actual_owner_correction_rows':6,'public_unchanged_rows_reused_verbatim':14,'public_context_corrected_tangent_rows':2,'all_selected_raw_lines_copied_byte_for_byte':True,'serialized_rows_or_nodes_modified':False,'raw_first_capture_and_differences_retained':True,'per_root_captures':[{'module':k[0],'name':k[1],'original_final_row_sha256':sha(original_final[k]),'public_final_row_sha256':sha(public_final[k]),'original_source':'original-owner-corrected-six.jsonl' if k in old_correction else 'original-unfiltered-selected.jsonl','public_source':'tangent-corrected-context-all.jsonl' if k in new_tangent else 'public-unfiltered-all.jsonl'} for k in original_final]},indent=2)+'\n')
print('ASSEMBLED_ALL16_ACTUAL_PUBLIC_ROOTS_WITH_VERBATIM_CAPTURE_ROWS')
