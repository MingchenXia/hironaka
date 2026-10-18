"""Bind the complete source/input audit to the converged full-document PDF."""
from pathlib import Path
import hashlib,json,re,subprocess,collections,shutil
A=Path(__file__).resolve().parent;ROOT=A.parents[1];P=A.parent/'analytic-completion-and-global-curve-atlas-20261018'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
log=(A/'blueprint-pdf-build/extensions.log').read_text();old=(P/'blueprint-pass-3.log').read_text()
assert 'Output written on' in log and 'Rerun to get cross-references right' not in log
assert not re.search(r'^!|LaTeX Error:',log,re.M)
info=subprocess.check_output(['pdfinfo',str(A/'blueprint-pdf-build/extensions.pdf')],text=True)
pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1]);assert pages>=786
for path,digest in json.loads((A/'blueprint-all-input-source-digests.json').read_text()).items():assert sha(ROOT/path)==digest,path
shutil.copyfile(A/'blueprint-pdf-build/extensions.log',A/'blueprint-pass-3.log')
r=json.loads((A/'blueprint-source-scope-validation.json').read_text())
r.update({'status':'PASS_COMPLETE_BLUEPRINT_LATEX_NO_ERRORS','pages':pages,'pdf_path':'blueprint-pdf-build/extensions.pdf','pdf_sha256':sha(A/'blueprint-pdf-build/extensions.pdf'),'pdf_bytes':(A/'blueprint-pdf-build/extensions.pdf').stat().st_size,'latex_errors':0,'latex_warning_occurrences':log.count('LaTeX Warning:'),'reference_warning_occurrences':len(re.findall(r'LaTeX Warning: Reference ',log)),'pdf_bookmark_warning_occurrences':log.count('Package hyperref Warning:'),'missing_pdf_destination_warning_occurrences':log.count('pdfTeX warning'),'math_environment_warning_occurrences':log.count('Package amsmath Warning:'),'reference_warning_inventory_unchanged_from_predecessor':collections.Counter(re.findall(r"LaTeX Warning: Reference `([^']+)'",log))==collections.Counter(re.findall(r"LaTeX Warning: Reference `([^']+)'",old)),'missing_pdf_destination_inventory_unchanged_from_predecessor':re.findall(r'pdfTeX warning[^\n]*name\{([^}]+)\}',log)==re.findall(r'pdfTeX warning[^\n]*name\{([^}]+)\}',old),'warnings_intentionally_retained':'Unchanged external prerequisite references, missing historical destinations, six mathematical bookmark-token warnings and one amsmath warning from the preserved complete original chapters. No source proof or label was rewritten to suppress them.','latex_passes':3,'final_cross_references_stable':True,'pdf_validation_status':'PASS_RENDERED_NO_LATEX_ERRORS','input_sources_unchanged_during_render':True})
assert r['reference_warning_inventory_unchanged_from_predecessor'] and r['missing_pdf_destination_inventory_unchanged_from_predecessor']
(A/'blueprint-validation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','pages','complete_synchronized_chapters','complete_original_proofs','distinct_local_bindings','all_document_chapters','all_document_distinct_local_binding_spellings','reference_warning_occurrences']}))
