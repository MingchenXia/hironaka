"""Read-only full blueprint source/input audit; no Lean invocation or proof edits."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['','2','3','4']])
from upstream_blueprint_scope import annotate
sha=lambda raw:hashlib.sha256(raw).hexdigest()
load=lambda path:json.loads(path.read_text())
BASE='7077e5469e0d6a5ce3a95e51b5e7400dc2d906ec'
SOURCE=Path('/workspace/archon-nakamaye-publish');REV='7266ce19c9d3f79a8693f7ded964755af7af59a7'
previous=ROOT/'audit/analytic-coefficient-dictionary-and-chosen-overlaps-20261015'
old=load(previous/'complete-synchronized-blueprint-paths.json');new=load(HERE/'blueprint-provenance.json')
paths=old+[r['destination_path'] for r in new]
assert len(old)==357 and len(new)==33 and len(set(paths))==len(paths)==390
external=load(ROOT/'scripts/upstream_blueprint_external_bindings.json')
unbound=load(ROOT/'scripts/upstream_blueprint_unbound_bindings.json')
typography=load(ROOT/'scripts/upstream_blueprint_typography.json')
for path in old:
    before=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path])
    assert (ROOT/path).read_bytes()==before,path
for rec in new:
    raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+rec['source_path']])
    assert sha(raw)==rec['source_sha256']
    out=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
    for change in typography.get(Path(rec['destination_path']).name,[]):
        assert out.count(change['before'])==1
        out=out.replace(change['before'],change['after'])
    out=annotate(out,external,unbound)
    actual=(ROOT/rec['destination_path']).read_bytes()
    assert actual==out.encode() and sha(actual)==rec['destination_sha256']
    proofs=re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',out)
    assert len(proofs)==rec['proofs']==raw.decode().count('\\begin{proof}')
    assert all(p.strip() for p in proofs)
def refs(text,kind='lean'):
    return {r.strip() for z in re.findall(r'\\'+kind+r'\{([^}]+)\}',text) for r in z.split(',')}
text=lambda ps:'\n'.join((ROOT/p).read_text() for p in ps)
oldtext=text(old);newtext=text([r['destination_path'] for r in new]);alltext=text(paths)
oldlocal=refs(oldtext);newlocal=refs(newtext);local=refs(alltext)
assert len(oldlocal)==4074 and len(newlocal)==175 and len(local)==4249 and not oldlocal&newlocal
assert newlocal==set(load(HERE/'new-local-bindings.json'))
upstream=refs(alltext,'upstreamlean');historical=refs(alltext,'upstreamunbound')
assert len(upstream)==241 and len(historical)==2 and not upstream&historical
assert not local&set(external)
assert historical==set(unbound)
assert oldtext.count('\\begin{proof}')==1465 and newtext.count('\\begin{proof}')==76
assert alltext.count('\\begin{proof}')==1541
main=ROOT/'blueprint/extensions.tex';master=main.read_text();inputs=re.findall(r'\\input\{([^}]+)\}',master)
assert len(inputs)==len(set(inputs))==475
fullpaths=['blueprint/'+p+'.tex' for p in inputs]
assert all((ROOT/p).is_file() for p in fullpaths) and set(paths)<=set(fullpaths)
fulltext=text(fullpaths);fullnames=refs(fulltext)
assert len(fullnames)==5408 and local<=fullnames
assert fulltext.count('\\begin{proof}')==fulltext.count('\\end{proof}')==2012
for word in ['390 complete synchronized','1,541 original proofs','4,492 distinct','4,249 local',REV,'879b6a01452b3d57b502d3f3568df2876f816d66']:
    assert word in master,word
(HERE/'complete-synchronized-blueprint-paths.json').write_text(json.dumps(paths,indent=2)+'\n')
(HERE/'complete-blueprint-local-bindings.json').write_text(json.dumps(sorted(local),indent=2)+'\n')
(HERE/'all-document-local-bindings.json').write_text(json.dumps(sorted(fullnames),indent=2)+'\n')
inputsnapshot={p:sha((ROOT/p).read_bytes()) for p in ['blueprint/extensions.tex']+fullpaths}
(HERE/'blueprint-all-input-source-digests.json').write_text(json.dumps(inputsnapshot,indent=2)+'\n')
compiled_log=(HERE/'all-actual-roots-final.log').read_text()
assert 'ALL_LIBRARY_MODULES 1003; ALL_LIBRARY_ACTUAL_ROOTS 16863; NEW_MODULES 34; NEW_ACTUAL_ROOTS 292; EXACT_BINDINGS 175; MISSING 0; STANDARD_THREE_ONLY' in compiled_log
assert 'SYNCHRONIZED_BLUEPRINT_EXACT_LOCAL_BINDINGS 4249; MISSING 0' in compiled_log
assert 'ALL_DOCUMENT_BLUEPRINT_EXACT_LOCAL_BINDINGS 5408; MISSING 0' in compiled_log
old_master=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':blueprint/extensions.tex'],text=True)
old_inputs=re.findall(r'\\input\{([^}]+)\}',old_master)
assert len(old_inputs)==442
for stem in old_inputs:
    path='blueprint/'+stem+'.tex'
    before=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path])
    assert (ROOT/path).read_bytes()==before,path
receipt={'status':'PASS_BLUEPRINT_SOURCE_SCOPE_AND_ALL_DOCUMENT_INPUTS_ONLY',
 'native_accepted_checkpoint':'879b6a01452b3d57b502d3f3568df2876f816d66','normal_published_revision':REV,
 'complete_synchronized_chapters':390,'complete_original_proofs':1541,'distinct_local_bindings':4249,
 'verified_upstream_only_bindings':241,'explicit_historical_unresolved_bindings':2,
 'distinct_synchronized_references':4492,'previous_synchronized_chapters':357,'previous_complete_proofs':1465,
 'previous_local_bindings':4074,'new_chapters':33,'new_complete_original_proofs':76,'new_local_bindings':175,
 'new_bindings_overlap_with_previous':0,'preceding_synchronized_chapter_sources_byte_identical':357,
 'new_chapters_replay_complete_normal_published_source':33,'all_document_chapters':475,
 'all_document_complete_proof_environments':2012,'all_document_distinct_local_binding_spellings':5408,
 'earlier_original_extension_chapters_outside_synchronized_scope':85,
 'additional_original_extension_binding_spellings_outside_synchronized_scope':1159,
 'all_inputs_exist_and_are_unique':True,'all_442_preceding_document_input_sources_byte_identical':True,'private_reference_derivatives_exported':False,
 'master_documentation_scope_update_only':load(HERE/'master-documentation-contexts.json'),
 'input_source_digests_file':'blueprint-all-input-source-digests.json','input_source_digests_sha256':sha((HERE/'blueprint-all-input-source-digests.json').read_bytes()),
 'compiled_binding_and_axiom_probe_status':'PASS_ALL_16863_ACTUAL_ROOTS_STANDARD_THREE_AND_ALL_5408_LOCAL_BINDINGS; all-actual-roots-final.log',
 'pdf_validation_status':'PENDING_SEPARATE_PDF_RECEIPT'}
(HERE/'blueprint-source-scope-validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='master_documentation_scope_update_only'}))
