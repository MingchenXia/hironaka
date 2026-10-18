"""Replay all seven support modules from fixed normal published Git; no native ledger."""
from pathlib import Path
import argparse,ast,hashlib,json,re,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--source-root',type=Path,required=True);args=p.parse_args()
A=Path(__file__).resolve().parent;ROOT=A.parents[1];REV='bae7068afc70d624cd8563fd4291436195a7f25f'
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'))
def published(path):return subprocess.check_output(['git','-C',str(args.source_root),'show',REV+':'+path])
rows=[]
for r in json.loads((A/'original-major-support-provenance.json').read_text()):
 raw=published(r['source_parent_path']);assert sha(raw)==r['source_parent_sha256'];joined=r['original_context_source']
 assert sha(joined.encode())==r['original_context_sha256']
 for d in r['complete_original_declarations']:
  lo,hi=d['source_byte_range'];block=raw[lo:hi];assert sha(block)==d['complete_original_declaration_sha256']
  assert block==(A/d['complete_original_declaration']).read_bytes();assert joined.count(block.decode())==1
 if r['destination_module'].endswith('FormalStandardMonomialHSComplementExact'):
  omitted=r['recorded_context_omissions'][0]['omitted_original_declaration'];lo,hi=omitted['source_byte_range'];block=raw[lo:hi]
  assert sha(block)==omitted['complete_original_declaration_sha256'];assert raw.decode().replace(block.decode(),'',1)==joined
  old=ROOT/r['recorded_context_omissions'][0]['published_source'];assert old.read_text().count(relocate(block.decode()))==1
 if r['destination_module'].endswith('TranslatedInitialHSOriginalExact'):assert joined.encode()==raw
 expected='/- Complete original prerequisites; statements and mathematical proofs are unchanged. -/\n'+''.join('import '+m+'\n' for m in r['pure_existing_or_new_original_support_imports'])+'\n'+relocate(joined)
 for c in r['declaration_local_original_instance_contexts']:
  assert expected.count(c['before'])==1;expected=expected.replace(c['before'],c['after'],1)
 actual=(ROOT/r['destination_path']).read_bytes();assert actual==expected.encode() and sha(actual)==r['destination_sha256']
 rows.append({'module':r['destination_module'],'complete_original_declarations':len(r['complete_original_declarations']),'exact_complete_destination_source_replayed':True,'source_parent_sha256':sha(raw),'destination_sha256':sha(actual)})
r=json.loads((A/'stalk-support-provenance.json').read_text());raw=published(r['source_path']);assert sha(raw)==r['source_parent_sha256']
lo,hi=r['original_byte_context_line_range_one_based'];context=b''.join(raw.splitlines(keepends=True)[lo-1:hi]);assert sha(context)==r['original_byte_context_sha256']
assert context==(ROOT/r['original_byte_context_path']).read_bytes()
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
expected=header+'import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance\n\nset_option autoImplicit false\nnamespace Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS\nnoncomputable section\nopen HolGerm HironakaHolomorphicPointJets\n\n'+relocate(context.decode())+'\nend\nend Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS\n'
actual=(ROOT/r['destination_path']).read_bytes();assert actual==expected.encode() and sha(actual)==r['destination_sha256']
for d in r['complete_original_declarations']:
 sl,sc,el,ec=d['compiler_ilean_range_zero_based'][:4];ls=raw.decode().splitlines(keepends=True);block=''.join(ls[sl:el+1]);block=block[sc:len(block)-len(ls[el])+ec]
 assert sha(block.encode())==d['source_complete_declaration_sha256'];assert expected.count(relocate(block))==1
rows.append({'module':r['destination_module'],'complete_original_declarations':3,'exact_complete_destination_source_replayed':True,'source_parent_sha256':sha(raw),'destination_sha256':sha(actual)})
repair=ROOT/'audit/actual-point-bennett-major-reproducibility-20261018'
result=subprocess.run([sys.executable,str(repair/'verify_repaired_original_source.py'),'--source-root',str(args.source_root)],cwd=ROOT,check=True,capture_output=True,text=True)
(A/'prior-iterderiv-original-source-replay.log').write_text(result.stdout+result.stderr)
rr=json.loads((repair/'original-support-source-provenance.json').read_text());assert sha(published(rr['source_parent_path']))==rr['source_parent_sha256']
rows.append({'module':rr['destination_module'],'complete_original_declarations':2,'exact_complete_destination_source_replayed':True,'source_parent_sha256':rr['source_parent_sha256'],'destination_sha256':rr['destination_sha256'],'previous_independent_source_receipt':str((repair/'repaired-original-source-replay.json').relative_to(ROOT))})
assert len(rows)==7
receipt={'status':'PASS_ALL_SEVEN_COMPLETE_ORIGINAL_SUPPORT_SOURCE_REPLAYS','normal_published_source_revision':REV,'private_ledger_required':False,'native_current_build_required':False,'proof_type_token_edits':0,'modules':rows,'frozen_relocate_profile_sha256':sha(frozen.read_bytes())}
(A/'all-original-support-source-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
