from pathlib import Path
import re,json,hashlib,subprocess
A=Path(__file__).resolve().parents[2];R=A.parents[1];O=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
old=json.loads((O.parent/'attempt05/final-read-only-no-op-input-fingerprints.json').read_text())
P=json.loads((A/'provenance.json').read_text());B=json.loads((A/'blueprint-provenance.json').read_text())
part=json.loads((A/'deferred-complete-module-partition.json').read_text())
plan=json.loads((A/'initial-port-plan.json').read_text())
assert len(P)==323 and len(B)==309
assert len(part['deferred_complete_modules'])==2 and len(part['deferred_complete_blueprint_chapters'])==2
removed={x['destination_path']for x in part['deferred_complete_modules']+part['deferred_complete_blueprint_chapters']}
headers=[]
rep=json.loads((A/'attempt06-integration-before/repair.json').read_text());m=rep['scope'];path=m.replace('.','/')+'.lean'
headers.append((path,A/'new-source-context-restoration/attempt05-before06'/path,rep['before_sha256'],rep['namespace_selective_open_qualification_only']))
for row in json.loads((A/'attempt08-header-qualification/exact-delta.json').read_text())['files']:
 path=row['module'].replace('.','/')+'.lean'
 headers.append((path,A/'attempt08-header-qualification/before'/path,row['before_source_sha256'],row['commands']))
validated=[]
for path,cap,h,commands in headers:
 raw=cap.read_bytes();assert sha(raw)==h==old[path],path
 text=raw.decode();first=re.search(r'^\s*(?:(?:private|noncomputable|local)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|axiom|opaque)\b',text,re.M)
 assert first,path
 for cmd in commands:
  assert text.count(cmd['before'])==1 and text.index(cmd['before'])<first.start(),(path,cmd)
  assert cmd['before'].startswith('open ')and cmd['after'].startswith('open _root_.Hironaka.'),cmd
  text=text.replace(cmd['before'],cmd['after'],1)
 assert text.encode()==(R/path).read_bytes(),path
 validated.append({'path':path,'before_sha256':h,'after_sha256':sha(text.encode()),'header_only_namespace_qualifications':commands,'entire_remaining_file_byte_identical':True})
assert len(validated)==6 and sum(len(x['header_only_namespace_qualifications'])for x in validated)==12
production=lambda p:p=='Hironaka.lean'or p.startswith('Hironaka/')or p.startswith('blueprint/')
missing={p for p in old if production(p)and not(R/p).exists()}
changed={p for p in old if production(p)and(R/p).exists()and sha((R/p).read_bytes())!=old[p]}
assert missing==removed,(missing,removed)
assert changed=={'Hironaka.lean','blueprint/extensions.tex',*[x['path']for x in validated]},changed
full=A/part['full_candidate_snapshot']
root=(full/'candidate-files/Hironaka.lean').read_text();assert sha(root.encode())==old['Hironaka.lean']
for row in part['deferred_complete_modules']:
 line='import '+row['module']+'\n';assert root.count(line)==1;root=root.replace(line,'',1)
extras=part['publication_extra_direct_imports'];assert extras==['Hironaka.Resolution.HironakaOriginalTerminalProperProjection']
assert all(x in {r['destination_module']for r in P}for x in extras)
assert root.count('\n/-!')==1
root=root.replace('\n\n/-!',''.join('\nimport '+m for m in extras)+'\n\n/-!',1)
assert root.encode()==(R/'Hironaka.lean').read_bytes()
master=(full/'candidate-files/blueprint/extensions.tex').read_text();assert sha(master.encode())==old['blueprint/extensions.tex']
for row in part['deferred_complete_blueprint_chapters']:
 line='\\input{'+Path(row['destination_path']).stem+'}\n';assert master.count(line)==1;master=master.replace(line,'',1)
assert master.encode()==(R/'blueprint/extensions.tex').read_bytes()
assert len(re.findall(r'\\input\{',master))==929
for path,h in plan['existing_destination_math_source_digests'].items():assert sha((R/path).read_bytes())==h,path
for path,h in plan['existing_blueprint_tex_digests'].items():
 if path!='blueprint/extensions.tex':assert sha((R/path).read_bytes())==h,path
for path,h in plan['toolchain_profiles'].items():assert sha((R/path).read_bytes())==h,path
physical={str(p.relative_to(R))for p in (R/'Hironaka').rglob('*.lean')}|{'Hironaka.lean'}
expected=set(plan['existing_destination_math_source_digests'])|{x['destination_path']for x in P}|{'Hironaka.lean'}
assert physical==expected and len(physical)==1483,(len(physical),len(expected),physical^expected)
by_module={p.removesuffix('.lean').replace('/','.')for p in physical}
imports={p.removesuffix('.lean').replace('/','.'):re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',(R/p).read_text(),re.M)for p in physical}
seen=set()
def visit(m):
 if m in seen:return
 assert m in by_module,m
 seen.add(m)
 for dep in imports[m]:
  if dep=='Hironaka'or dep.startswith('Hironaka.'):visit(dep)
visit('Hironaka');assert seen==by_module,(len(seen),by_module-seen)
deferred_names={r['module']for r in part['deferred_complete_modules']}
assert not any(deferred_names.intersection(deps)for deps in imports.values())
labels=set();deferred_valid=[]
for row in part['deferred_complete_modules']+part['deferred_complete_blueprint_chapters']:
 raw=(A/row['canonical_draft_capture']).read_bytes();assert sha(raw)==row['sha256'];assert not(R/row['destination_path']).exists()
 assert (full/'candidate-files'/row['destination_path']).read_bytes()==raw
 if row['destination_path'].endswith('.tex'):
  text=raw.decode();labels.update(re.findall(r'\\label\{([^}]+)\}',text))
  assert text.count('\\begin{proof}')==row['complete_written_proofs']
 deferred_valid.append({'path':row['destination_path'],'capture':row['canonical_draft_capture'],'sha256':row['sha256']})
assert len(labels)==7
for f in (R/'blueprint').glob('*.tex'):
 text=f.read_text()
 refs={v.strip()for group in re.findall(r'\\(?:uses|ref|eqref)\{([^}]+)\}',text)for v in group.split(',')}
 assert not refs.intersection(labels),(f,refs&labels)
 binds=[v.strip()for group in re.findall(r'\\lean\{([^}]+)\}',text)for v in group.split(',')]
 assert not any('HironakaOriginalGlobalOffZero.'in v or'HironakaOriginalGlobalProperModification.'in v for v in binds),f
assert sum(r['proofs']for r in B)==988
# Retained source-facing BP records carry identical complete bytes to candidate325.
for row in B:
 assert(R/row['destination_path']).read_bytes()==(full/'candidate-files'/row['destination_path']).read_bytes(),row['destination_path']
result={'status':'PASS_EXACT_05_TO_08_HEADER_ONLY_ADMINISTRATION_AND_WHOLE_MODULE_PARTITION','candidate':8,'fixed_ordinary_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','header_qualified_files':validated,'header_qualifications':12,'original_statement_proof_payload_edits':0,'whole_deferred_source_and_blueprint':deferred_valid,'whole_deferred_nodes_and_proofs':7,'whole_deferred_literal_bindings':11,'retained_source_records':323,'retained_whole_original_modules':305,'complete_original_complements':7,'pure_existing_support_adapters':2,'complete_original_support_extracts':9,'retained_source_facing_BP_chapters':309,'retained_whole_original_BP_chapters':306,'retained_complete_original_node_extract_chapters':3,'retained_written_proofs':988,'master_inputs':929,'old_mathematical_sources_byte_preserved':len(plan['existing_destination_math_source_digests']),'old_BP_chapters_byte_preserved':len(plan['existing_blueprint_tex_digests'])-1,'frozen_profiles_preserved':len(plan['toolchain_profiles']),'all_physical_Lean_sources_reachable_from_umbrella':1483,'extra_direct_umbrella_import':extras,'other_retained_production_source_BP_byte_unchanged_from05':True,'retained_BP_whole_candidate_bytes_unchanged':True,'remaining_references_to_deferred_labels_or_modules':[],'Lean_kernel_Expr_runtime_replayed':False}
f=O/'exact-05-to-08-static-delta.json';assert not f.exists();f.write_text(json.dumps(result,indent=2)+'\n');print(f);print(sha(f.read_bytes()))
