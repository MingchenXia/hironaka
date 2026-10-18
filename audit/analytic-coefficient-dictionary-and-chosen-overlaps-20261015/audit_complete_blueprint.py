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
BASE='3aa1692af186967f63d4197a34114d6e316aed95'
SOURCE=Path('/workspace/archon-nakamaye-publish');REV='09dc511c4a14836a0287748d1a63f9f467f677d3'
previous=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015'
old=load(previous/'complete-synchronized-blueprint-paths.json');new=load(HERE/'blueprint-provenance.json')
paths=old+[r['destination_path'] for r in new]
assert len(old)==319 and len(new)==38 and len(set(paths))==len(paths)==357
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
assert len(oldlocal)==3533 and len(newlocal)==541 and len(local)==4074 and not oldlocal&newlocal
assert newlocal==set(load(HERE/'new-local-bindings.json'))
upstream=refs(alltext,'upstreamlean');historical=refs(alltext,'upstreamunbound')
assert len(upstream)==241 and len(historical)==2 and not upstream&historical
assert not local&set(external)
assert historical==set(unbound)
assert oldtext.count('\\begin{proof}')==1302 and newtext.count('\\begin{proof}')==163
assert alltext.count('\\begin{proof}')==1465
main=ROOT/'blueprint/extensions.tex';master=main.read_text();inputs=re.findall(r'\\input\{([^}]+)\}',master)
assert len(inputs)==len(set(inputs))==442
fullpaths=['blueprint/'+p+'.tex' for p in inputs]
assert all((ROOT/p).is_file() for p in fullpaths) and set(paths)<=set(fullpaths)
fulltext=text(fullpaths);fullnames=refs(fulltext)
assert len(fullnames)==5233 and local<=fullnames
assert fulltext.count('\\begin{proof}')==fulltext.count('\\end{proof}')==1936
for word in ['357 complete synchronized','1,465 original proofs','4,317 distinct','4,074 local',REV,'db4e4065403b4ab8b077fac41985825931e5cc02']:
    assert word in master,word
(HERE/'complete-synchronized-blueprint-paths.json').write_text(json.dumps(paths,indent=2)+'\n')
(HERE/'complete-blueprint-local-bindings.json').write_text(json.dumps(sorted(local),indent=2)+'\n')
(HERE/'all-document-local-bindings.json').write_text(json.dumps(sorted(fullnames),indent=2)+'\n')
inputsnapshot={p:sha((ROOT/p).read_bytes()) for p in ['blueprint/extensions.tex']+fullpaths}
(HERE/'blueprint-all-input-source-digests.json').write_text(json.dumps(inputsnapshot,indent=2)+'\n')
receipt={'status':'PASS_BLUEPRINT_SOURCE_SCOPE_AND_ALL_DOCUMENT_INPUTS_ONLY',
 'native_accepted_checkpoint':'db4e4065403b4ab8b077fac41985825931e5cc02','normal_published_revision':REV,
 'complete_synchronized_chapters':357,'complete_original_proofs':1465,'distinct_local_bindings':4074,
 'verified_upstream_only_bindings':241,'explicit_historical_unresolved_bindings':2,
 'distinct_synchronized_references':4317,'previous_synchronized_chapters':319,'previous_complete_proofs':1302,
 'previous_local_bindings':3533,'new_chapters':38,'new_complete_original_proofs':163,'new_local_bindings':541,
 'new_bindings_overlap_with_previous':0,'preceding_synchronized_chapter_sources_byte_identical':319,
 'new_chapters_replay_complete_normal_published_source':38,'all_document_chapters':442,
 'all_document_complete_proof_environments':1936,'all_document_distinct_local_binding_spellings':5233,
 'earlier_original_extension_chapters_outside_synchronized_scope':85,
 'additional_original_extension_binding_spellings_outside_synchronized_scope':1159,
 'all_inputs_exist_and_are_unique':True,'private_reference_derivatives_exported':False,
 'master_documentation_scope_update_only':load(HERE/'blueprint-master-scope-update.json'),
 'input_source_digests_file':'blueprint-all-input-source-digests.json','input_source_digests_sha256':sha((HERE/'blueprint-all-input-source-digests.json').read_bytes()),
 'compiled_binding_and_axiom_probe_status':'PENDING_ROOT_FINAL_GATES; no Lean invoked by this audit',
 'pdf_validation_status':'PENDING_SEPARATE_PDF_RECEIPT'}
(HERE/'blueprint-source-scope-validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='master_documentation_scope_update_only'}))
