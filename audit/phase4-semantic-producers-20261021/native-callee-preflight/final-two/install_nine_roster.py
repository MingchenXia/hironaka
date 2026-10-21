from pathlib import Path
import hashlib,json,shutil,subprocess
D=Path('/workspace/hironaka');A=D/'audit/phase4-semantic-producers-20261021';W=Path(__file__).resolve().parent;REV='636442a87402a67de1f914cb4120ee28c3ed6ad7';H=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((A/'provenance.json').read_text());bps=json.loads((A/'blueprint-provenance.json').read_text());assert len(rows)==len(bps)==7
K=json.loads((A/'new-kernel-status.json').read_text());assert K['passed']==K['total']==7
E=json.loads((A/'final-per-module-expressions/status.json').read_text());assert E['captured_and_compared_modules']==7
snapshot=A/'frozen-seven-before-append';assert not snapshot.exists();snapshot.mkdir()
manifest={}
for name in ['cohort-plan.json','provenance.json','blueprint-provenance.json','source-replay-receipt.json','new-kernel-status.json','exact-module-renames.tsv','original-elaboration-contexts.json','sync_phase4_cohort.py','final-per-module-expressions/status.json']:
 p=A/name;q=snapshot/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());manifest[str(p.relative_to(D))]=H(p.read_bytes())
for p in [D/'Hironaka.lean',D/'blueprint/extensions.tex']:
 q=snapshot/('before-nine-'+p.name);q.write_bytes(p.read_bytes());manifest[str(p.relative_to(D))]=H(p.read_bytes())
for r in rows+bps:
 p=D/r['destination_path'];q=snapshot/r['destination_path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());assert H(p.read_bytes())==r['destination_sha256'];manifest[r['destination_path']]=H(p.read_bytes())
for m,r in K['modules'].items():
 for part in r['kernel_parts']:manifest[part['path']]=part['sha256'];assert H((D/part['path']).read_bytes())==part['sha256']
for m,r in E['modules'].items():
 for v in r['captures'].values():manifest[v['path']]=v['gzip_sha256'];assert H((D/v['path']).read_bytes())==v['gzip_sha256']
(snapshot/'manifest.json').write_text(json.dumps({'status':'FROZEN_SEVEN_STAGE_SOURCE_KERNEL_AND_UNFILTERED_CAPTURE_INPUTS','files':manifest,'source_modules':7,'native_original_captures_reused_after_three_ENat_contexts':True},indent=2)+'\n')
# Source-facing external pointer is a separately counted new documentation input.
sp='TranscendentalNakamaye/blueprint/src/hironaka.tex';raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',REV+':'+sp]);assert raw.count(b'\\label{hir:base-change-open}')==1
cap=A/'original-whole-source-captures/hironaka.tex-external-prerequisite.txt';cap.write_bytes(raw)
index='\n'.join([r'\section{External prerequisite for the new semantic producers}',r'\label{sec:phase4-external-prerequisites-20261021}',r'The following label points to the complete original prerequisite in the fixed native source. This documentation pointer does not assert an additional locally exported theorem.',r'\label{hir:base-change-open}',r'\href{https://github.com/MingchenXia/archon-nakamaye/blob/'+REV+'/'+sp+r'#L5438}{Original open base-change statement and proof, fixed revision '+REV[:7]+r'.}'])+'\n'
idx=A/'phase4-external-prerequisite-index.tex.txt';idx.write_text(index)
plan=json.loads((A/'cohort-plan.json').read_text());plan.update(authoring_ledger_revision='89b102c2146f4d12a7852e569eb8ddeab05928c1',ordinary_published_revision=REV,source_modules=9,BP_chapters=9,new_written_proofs=28,source_pin_kind='FIXED_ORDINARY_GIT_REVISION_SOURCE_AND_BP_BYTES_CHECKED',documentation_external_prerequisites=[{'destination_path':'blueprint/phase4-external-prerequisites-20261021.tex','generated_text':'phase4-external-prerequisite-index.tex.txt','destination_sha256':H(index.encode()),'labels':['hir:base-change-open'],'source_path':sp,'source_sha256':H(raw),'raw_capture':str(cap.relative_to(A))}],approved_root_master_append_states={'Hironaka.lean':{'path':'frozen-seven-before-append/before-nine-Hironaka.lean','sha256':manifest['Hironaka.lean']},'blueprint/extensions.tex':{'path':'frozen-seven-before-append/before-nine-extensions.tex','sha256':manifest['blueprint/extensions.tex']}})
(A/'cohort-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
for out,src in [('provenance.json','candidate-nine-provenance.json'),('blueprint-provenance.json','candidate-nine-blueprint-provenance.json')]: (A/out).write_bytes((W/src).read_bytes())
(A/'native-actual-callee-preflight.json').write_bytes((W/'nine-actual-callee-import-visibility.json').read_bytes())
newrows=json.loads((A/'provenance.json').read_text())[-2:];renames=A/'exact-module-renames.tsv';renames.write_text(''.join(r['source_module']+'\t'+r['destination_module']+'\n'for r in newrows)+renames.read_text())
p=A/'sync_phase4_cohort.py';s=p.read_text().replace("default='52e93b1998d2bff0e24251c92d0dd6f7d882e3e0'",f"default='{REV}'")
s=s.replace("for row in rows:\n out=header", "for row in plan.get('documentation_external_prerequisites',[]):\n original(row);out=(A/row['generated_text']).read_text();assert h(out.encode())==row['destination_sha256'];install(row['destination_path'],out)\nfor row in rows:\n out=header")
s=s.replace("for b in bps)+oldmaster[at:]", "for b in [*bps,*plan.get('documentation_external_prerequisites',[])])+oldmaster[at:]")
s=s.replace("current=(D/path).read_text();assert current in [before,after],('Unexpected root/master modification',path)","current=(D/path).read_text();allowed=[before,after];approval=plan.get('approved_root_master_append_states',{}).get(path)\n if approval:\n  approved=(A/approval['path']).read_text();assert h(approved.encode())==approval['sha256'];allowed.append(approved)\n assert current in allowed,('Unexpected root/master modification',path)")
s=s.replace("'complete_original_chapters':len(bps),", "'complete_original_chapters':len(bps),'additional_documentation_pointer_inputs':len(plan.get('documentation_external_prerequisites',[])),")
p.write_text(s)
compile(s,str(p),'exec')
print('FROZEN_SEVEN_AND_PREPARED_NINE_ORDINARY_SOURCE_ROSTER',REV)
