"""Audit exact original443 chapters, synchronized union, and complete document.

Report inherited unsupported statement locations verbatim without repairing or
waiving them. Exact compiled bindings and PDF rendering are separate gates.
"""
from pathlib import Path
import collections,hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
OLD=ROOT/'audit/surface-bennett-and-compact-ordered-curves-20261018'
SOURCE=Path('/workspace/archon-nakamaye-main');REV='6a888f9dc4155b9ec1407b27223eb37218957159'
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
from blueprint_statement_scope import inspect,STATEMENT
sha=lambda raw:hashlib.sha256(raw).hexdigest()
load=lambda p:json.loads(p.read_text())
def save(name,obj):(A/name).write_text(json.dumps(obj,indent=2)+'\n')
def refs(text,kind='lean'):return{n.strip()for group in re.findall(r'\\'+kind+r'\{([^}]+)\}',text)for n in group.split(',')}
def findings(paths):
 out=[]
 for path in paths:
  text=(ROOT/path).read_text()
  try:inspect(text)
  except AssertionError as exc:
   accounted={label for block in STATEMENT.finditer(text)for label in re.findall(r'\\label\{([^}]+)\}',block[2])}
   labels=set(re.findall(r'\\label\{([^}]+)\}',text))
   out.append({'path':path,'source_sha256':sha(text.encode()),'strict_inspector_failure':str(exc)or'Statement inspector label coverage differs from all source labels','labels_outside_supported_statement_environments':sorted(labels-accounted),'source_label_lines':{label:text[:text.index('\\label{'+label+'}')].count('\n')+1 for label in sorted(labels-accounted)}})
 return out

names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
for path,h in load(A/'frozen-source-profile-sha256.json')['profiles'].items():assert sha((ROOT/path).read_bytes())==h,path
old=load(OLD/'complete-synchronized-blueprint-paths.json');assert len(old)==516
new=load(A/'complete-blueprint-provenance.json');assert len(new)==18
paths=list(dict.fromkeys(old+[r['destination_path']for r in new]));assert len(paths)==534
external=load(ROOT/'scripts/upstream_blueprint_external_bindings.json');unbound=load(ROOT/'scripts/upstream_blueprint_unbound_bindings.json');typography=load(ROOT/'scripts/upstream_blueprint_typography.json')
old_digests=load(OLD/'blueprint-all-input-source-digests.json');old_full=[p for p in old_digests if p!='blueprint/extensions.tex'];assert len(old_full)==601
for path in old_full:assert sha((ROOT/path).read_bytes())==old_digests[path],path
subprocess.run([sys.executable,str(A/'sync_frozen_443.py'),'--check'],cwd=ROOT,check=True)
subprocess.run([sys.executable,str(A/'recover_original_prerequisites.py'),'--check'],cwd=ROOT,check=True)
scope={}
for r in new:
 raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+r['source_path']]);assert sha(raw)==r['source_sha256']
 selected=raw.decode()
 if r.get('source_kind')=='complete_original_statement_and_proof_fragment':
  selected=r['selected_original_source'];assert selected in raw.decode()and sha(selected.encode())==r['selected_original_source_sha256']
 output=names.rename_text_names(selected).replace('\\chapter{','\\section{')
 for change in typography.get(Path(r['destination_path']).name,[]):
  assert output.count(change['before'])==1;output=output.replace(change['before'],change['after'])
 output=annotate(output,external,unbound);actual=(ROOT/r['destination_path']).read_text()
 if r.get('source_kind')=='complete_original_statement_and_proof_fragment':assert output in actual
 else:assert actual==output
 assert sha(actual.encode())==r['destination_sha256']
 assert actual.count('\\begin{proof}')==selected.count('\\begin{proof}')==r['proofs']
 scope[r['destination_path']]=inspect(actual)
assert sum(len(xs)for xs in scope.values())==48
assert sum(r['complete_proofs']for xs in scope.values()for r in xs)==48
assert sum(r['kind']=='definition'for xs in scope.values()for r in xs)==1
text=lambda ps:'\n'.join((ROOT/p).read_text()for p in ps)
previous=text(old);increment=text([r['destination_path']for r in new]);synchronized=text(paths)
old_local,new_local,local=refs(previous),refs(increment),refs(synchronized)
assert new_local==set(load(A/'all-new-local-bindings.json'))and len(new_local)==73
assert len(old_local)==4899 and previous.count('\\begin{proof}')==1870
assert synchronized.count('\\begin{proof}')==1918
upstream,historical=refs(synchronized,'upstreamlean'),refs(synchronized,'upstreamunbound')
assert historical==set(unbound)and not local.intersection(external)and not upstream.intersection(historical)
master=(ROOT/'blueprint/extensions.tex').read_text();stems=re.findall(r'\\input\{([^}]+)\}',master);full=['blueprint/'+s+'.tex'for s in stems]
assert len(stems)==len(set(stems))==619 and all((ROOT/p).is_file()for p in full)and set(paths).issubset(full)
complete=text(full);all_local=refs(complete);proofs=re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',complete)
assert len(proofs)==complete.count('\\begin{proof}')==complete.count('\\end{proof}')==2389 and all(p.strip()for p in proofs)
old_findings=findings(old_full);full_findings=findings(full);assert full_findings==old_findings and len(full_findings)==36
labels=re.findall(r'\\label\{([^}]+)\}',complete);dups={s:n for s,n in collections.Counter(labels).items()if n>1}
save('complete-synchronized-blueprint-paths.json',paths);save('complete-blueprint-local-bindings.json',sorted(local));save('all-document-local-bindings.json',sorted(all_local));save('docs-new-statement-proof-scope.json',scope)
save('blueprint-all-input-source-digests.json',{p:sha((ROOT/p).read_bytes())for p in ['blueprint/extensions.tex']+full})
save('docs-inherited-statement-scope-findings.json',{'status':'INHERITED_STRICT_INSPECTOR_FINDINGS_UNCHANGED_FROM_601_INPUT_PREDECESSOR','all_document_findings':full_findings,'synchronized_findings':[r for r in full_findings if r['path']in paths],'new18_scope_findings':[],'definition_proofs_manufactured':0,'interpretation':'Historical label locations and historical statement-proof findings are retained verbatim; only all18 new complete original chapters and complete statement/proof extracts are claimed to pass labelled statement scope'})
result={'status':'PASS_COMPLETE_18_ORIGINAL_BLUEPRINTS_AND_NEW_STATEMENT_SCOPE_AND_FULL_DOCUMENT_PROOF_ENVIRONMENTS','normal_published_revision':REV,'native_accepted_checkpoint':'4774cd3a97737754b463603a2188df4cd48efd84','complete_synchronized_chapters':len(paths),'complete_original_proofs':synchronized.count('\\begin{proof}'),'distinct_local_bindings':len(local),'upstream_only_binding_spellings':len(upstream),'explicit_historical_unresolved_bindings':len(historical),'previous_synchronized_chapters':len(old),'previous_complete_proofs':previous.count('\\begin{proof}'),'previous_local_bindings':len(old_local),'provenance_chapters':len(new),'provenance_complete_original_proofs':increment.count('\\begin{proof}'),'provenance_local_bindings':len(new_local),'provenance_bindings_overlap_with_previous':len(old_local&new_local),'newly_added_binding_spellings':len(new_local-old_local),'provenance_labelled_statement_nodes':48,'provenance_labelled_definitions':1,'provenance_labelled_definitions_without_proof':0,'definition_proofs_manufactured':0,'preceding_document_chapter_sources_byte_identical':601,'all_document_chapters':len(full),'all_document_complete_proof_environments':len(proofs),'all_document_distinct_local_binding_spellings':len(all_local),'all_document_labels':len(labels),'all_document_duplicate_labels':dups,'all_inputs_exist_and_are_unique':True,'inherited_full_document_strict_statement_scope_findings':len(full_findings),'new_strict_statement_scope_findings':0,'full_document_strict_statement_scope_status':'HAS_36_INHERITED_FINDINGS; see docs-inherited-statement-scope-findings.json','compiled_binding_probe_status':'PENDING_SEPARATE_COMPILER_PROBE','axiom_probe_status':'PENDING_SEPARATE_ALL_MODULE_ROOT_PROBE','pdf_validation_status':'PENDING_SEPARATE_PDF_RECEIPT','publication_status':'PENDING_EXPRESSION_KERNEL_AND_INDEPENDENT_REVIEW_GATES'}
save('blueprint-source-scope-validation.json',result);print(json.dumps(result))
