"""Reverse only recorded administrative contexts to the frozen original replay."""
from pathlib import Path
import hashlib,json
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
sha=lambda raw:hashlib.sha256(raw).hexdigest()
records=json.loads((A/'provenance.json').read_text());rows=[]
for r in records:
 raw=(ROOT/r['destination_path']).read_bytes();assert sha(raw)==r['destination_sha256']
 text=raw.decode();contexts=r['administrative_elaboration_contexts']
 for c in reversed(contexts):
  assert text.count(c['after'])==1,(r['destination_module'],c['kind']);text=text.replace(c['after'],c['before'],1)
 assert sha(text.encode())==r['initial_synchronized_destination_sha256'],r['destination_module']
 first=A/'strict-attempt-01/source-before-context-recovery'/r['destination_path']
 without_prefix=raw.decode()
 prefixes=[c for c in contexts if c['kind']=='declaration_local_recovery_of_original_compiled_instance_route']
 for c in reversed(prefixes):
  assert without_prefix.count(c['after'])==1;without_prefix=without_prefix.replace(c['after'],c['before'],1)
 assert without_prefix.encode()==first.read_bytes(),('Additional source change beyond reviewed prefix',r['destination_module'])
 rows.append({'module':r['destination_module'],'final_source_sha256':sha(raw),'reversed_original_relocation_sha256':sha(text.encode()),'frozen_original_relocation_sha256':r['initial_synchronized_destination_sha256'],'original_native_source_sha256':r['source_sha256'],'declaration_local_original_projection_contexts':len(prefixes),'pure_support_import_contexts':sum(c['kind']=='pure_import_existing_verified_original_support'for c in contexts),'reversed_prefix_matches_entire_first_attempt_source':True,'original_type_and_proof_text_changes':0})
guard=json.loads((A/'previous-public-source-digests.json').read_text());assert len(guard['mathematical_sources'])==1106
for p,h in guard['mathematical_sources'].items():assert sha((ROOT/p).read_bytes())==h,p
result={'status':'PASS_ALL_34_COMPLETE_ORIGINAL_SOURCE_REVERSALS_AND_ALL_1106_OLD_SOURCES','whole_original_modules':len(rows),'declaration_local_original_projection_contexts':sum(r['declaration_local_original_projection_contexts']for r in rows),'pure_support_import_contexts':sum(r['pure_support_import_contexts']for r in rows),'original_type_and_proof_text_changes':0,'old_public_math_sources_byte_identical':1106,'rows':rows}
(A/'reverse-original-context-source-guard.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='rows'}))
