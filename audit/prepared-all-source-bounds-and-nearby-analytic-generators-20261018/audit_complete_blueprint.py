"""Check the complete fixed338 blueprint union and every full-document input."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
P=HERE.parent/'analytic-strict-generators-and-coupled-global-endpoint-20261018'
BASE='2342eead0cdd7bba08acb2456e275a916bab94cf'
REV='f873b1d904f8e63cd9f73e0b5bf6eefb0332093a'
CP='862e555f2c5289f9b29cb844461cda7a23618d7c'
SOURCE=Path('/workspace/archon-nakamaye-publish')
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
from blueprint_statement_scope import inspect
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['','2','3','4']])
prior=load(P/'blueprint-validation.json');plan=load(HERE/'frozen-extraction-plan.json')
old=load(P/'complete-synchronized-blueprint-paths.json');new=load(HERE/'blueprint-provenance.json')
paths=old+[r['destination_path'] for r in new]
assert len(old)==410 and len(new)==5 and len(paths)==len(set(paths))==415
external=load(ROOT/'scripts/upstream_blueprint_external_bindings.json')
unbound=load(ROOT/'scripts/upstream_blueprint_unbound_bindings.json')
typography=load(ROOT/'scripts/upstream_blueprint_typography.json')
for path in old:
 assert (ROOT/path).read_bytes()==subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path])
statement_scope={}
for rec in new:
 raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+rec['source_path']])
 assert hashlib.sha256(raw).hexdigest()==rec['source_sha256']
 out=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
 for change in typography.get(Path(rec['destination_path']).name,[]):
  assert out.count(change['before'])==1;out=out.replace(change['before'],change['after'])
 out=annotate(out,external,unbound);actual=(ROOT/rec['destination_path']).read_text()
 assert actual==out and sha(ROOT/rec['destination_path'])==rec['destination_sha256']
 assert out.count('\\begin{proof}')==raw.decode().count('\\begin{proof}')==rec['proofs']
 statement_scope[rec['destination_path']]=inspect(actual)
assert sum(len(v) for v in statement_scope.values())==13
assert sum(r['complete_proofs'] for rows in statement_scope.values() for r in rows)==12
assert sum(r['kind']=='definition' and r['complete_proofs']==0 for rows in statement_scope.values() for r in rows)==1
refs=lambda text,kind='lean':{v.strip() for group in re.findall(r'\\'+kind+r'\{([^}]+)\}',text) for v in group.split(',')}
text=lambda ps:'\n'.join((ROOT/p).read_text() for p in ps)
oldtext=text(old);newtext=text([r['destination_path'] for r in new]);alltext=text(paths)
oldlocal=refs(oldtext);newlocal=refs(newtext);local=refs(alltext)
assert len(oldlocal)==prior['distinct_local_bindings']==4313
assert len(newlocal)==plan['bindings']==22 and not oldlocal&newlocal and len(local)==4335
assert newlocal==set(load(HERE/'new-local-bindings.json'))
upstream=refs(alltext,'upstreamlean');historical=refs(alltext,'upstreamunbound')
assert len(upstream)==241 and len(historical)==2 and not local&set(external)
assert historical==set(unbound) and not upstream&historical
assert oldtext.count('\\begin{proof}')==prior['complete_original_proofs']==1581
assert newtext.count('\\begin{proof}')==plan['proofs']==12
assert alltext.count('\\begin{proof}')==1593
master=(ROOT/'blueprint/extensions.tex').read_text();inputs=re.findall(r'\\input\{([^}]+)\}',master)
assert len(inputs)==len(set(inputs))==500
fullpaths=['blueprint/'+p+'.tex' for p in inputs]
assert all((ROOT/p).is_file() for p in fullpaths) and set(paths)<=set(fullpaths)
fulltext=text(fullpaths);fullnames=refs(fulltext)
assert len(fullnames)==5494 and local<=fullnames
proofs=re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',fulltext)
assert len(proofs)==fulltext.count('\\begin{proof}')==fulltext.count('\\end{proof}')==2064
assert all(p.strip() for p in proofs)
for word in ['415 complete synchronized','1,593 original proofs','4,578 distinct','4,335 local',REV,CP]:assert word in master
for name,value in [('complete-synchronized-blueprint-paths.json',paths),('complete-blueprint-local-bindings.json',sorted(local)),('all-document-local-bindings.json',sorted(fullnames))]:
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
digests={p:sha(ROOT/p) for p in ['blueprint/extensions.tex']+fullpaths}
(HERE/'blueprint-all-input-source-digests.json').write_text(json.dumps(digests,indent=2)+'\n')
compiled=(HERE/'all-actual-roots-final.log').read_text()
assert re.search(r'ALL_LIBRARY_MODULES 1035; ALL_LIBRARY_ACTUAL_ROOTS [0-9]+; NEW_MODULES 8; NEW_ACTUAL_ROOTS [0-9]+; EXACT_BINDINGS 22; MISSING 0; STANDARD_THREE_ONLY', compiled)
assert 'SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4335; MISSING 0' in compiled
assert 'ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5494; MISSING 0' in compiled
oldmaster=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':blueprint/extensions.tex'],text=True)
oldinputs=re.findall(r'\\input\{([^}]+)\}',oldmaster);assert len(oldinputs)==495
for stem in oldinputs:
 path='blueprint/'+stem+'.tex';assert (ROOT/path).read_bytes()==subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path])
r={'status':'PASS_BLUEPRINT_SOURCE_SCOPE_AND_ALL_DOCUMENT_INPUTS_ONLY',
 'native_accepted_checkpoint':CP,'normal_published_revision':REV,
 'complete_synchronized_chapters':len(paths),'complete_original_proofs':alltext.count('\\begin{proof}'),
 'distinct_local_bindings':len(local),'verified_upstream_only_bindings':len(upstream),
 'explicit_historical_unresolved_bindings':len(historical),'distinct_synchronized_references':len(local|upstream|historical),
 'previous_synchronized_chapters':len(old),'previous_complete_proofs':oldtext.count('\\begin{proof}'),
 'previous_local_bindings':len(oldlocal),'new_chapters':len(new),'new_complete_original_proofs':newtext.count('\\begin{proof}'),
 'new_local_bindings':len(newlocal),'new_bindings_overlap_with_previous':0,
 'new_labelled_statement_nodes':13,'new_labelled_nondefinitions_with_complete_proofs':12,
 'new_labelled_definitions_without_proof':1,'new_definition_proofs_manufactured':0,
 'preceding_synchronized_chapter_sources_byte_identical':len(old),'new_chapters_replay_complete_normal_published_source':len(new),
 'all_document_chapters':len(fullpaths),'all_document_complete_proof_environments':len(proofs),
 'all_document_distinct_local_binding_spellings':len(fullnames),
 'earlier_original_extension_chapters_outside_synchronized_scope':len(fullpaths)-len(paths),
 'additional_original_extension_binding_spellings_outside_synchronized_scope':len(fullnames-local),
 'all_inputs_exist_and_are_unique':True,'all_495_preceding_document_input_sources_byte_identical':True,
 'private_reference_derivatives_exported':False,'master_documentation_scope_update_only':load(HERE/'master-documentation-contexts.json'),
 'input_source_digests_file':'blueprint-all-input-source-digests.json',
 'input_source_digests_sha256':sha(HERE/'blueprint-all-input-source-digests.json'),
 'compiled_binding_and_axiom_probe_status':'PASS_ALL_CURRENT_ACTUAL_ROOTS_STANDARD_THREE_AND_ALL_5494_LOCAL_BINDINGS; all-actual-roots-final.log',
 'pdf_validation_status':'PENDING_SEPARATE_PDF_RECEIPT'}
(HERE/'blueprint-source-scope-validation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='master_documentation_scope_update_only'}))
