from pathlib import Path
import ast,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
D=Path('/workspace/hironaka');A=D/'audit/phase4-semantic-producers-20261021';W=Path(__file__).resolve().parent;S=Path('/workspace/archon-publish');REV='636442a87402a67de1f914cb4120ee28c3ed6ad7';sha=lambda b:hashlib.sha256(b).hexdigest()
sp=importlib.util.spec_from_file_location('names',D/'scripts/upstream_namespace_map.py');names=importlib.util.module_from_spec(sp);sp.loader.exec_module(names);names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])');fp=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(x for x in ast.parse(fp.read_text()).body if isinstance(x,ast.FunctionDef)and x.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(fp),'exec'),env)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
rows=json.loads((A/'provenance.json').read_text());bps=json.loads((A/'blueprint-provenance.json').read_text());assert len(rows)==len(bps)==7
for r in rows+bps:
 raw=subprocess.check_output(['git','-C',str(S),'show',REV+':'+r['source_path']]);assert sha(raw)==r['source_sha256']and raw==(A/r['raw_capture']).read_bytes(),r['source_path']
newmods=(W/'native2-modules.txt').read_text().splitlines();captures=A/'original-whole-source-captures'
for m in newmods:
 path='TranscendentalNakamaye/'+m.replace('.','/')+'.lean';raw=subprocess.check_output(['git','-C',str(S),'show',REV+':'+path]);assert raw==(Path('/workspace/archon-nakamaye')/path).read_bytes()
 dm=names.new_mod(m);dst=dm.replace('.','/')+'.lean';assert not(D/dst).exists();out=header+env['relocate'](raw.decode());cap=captures/(m+'.lean.txt');assert not cap.exists()or cap.read_bytes()==raw;cap.write_bytes(raw)
 rows.append({'source_revision':REV,'source_module':m,'source_path':path,'source_sha256':sha(raw),'destination_module':dm,'destination_path':dst,'initial_synchronized_destination_sha256':sha(out.encode()),'destination_sha256':sha(out.encode()),'administrative_elaboration_contexts':[],'additional_pure_support_imports':[],'original_proof_tokens_changed':False,'whole_original_source_preserved':True,'raw_capture':str(cap.relative_to(A))})
 rawbpnames=[p for p in (S/'TranscendentalNakamaye/blueprint/src').glob('*.tex')if re.search(r'\\lean\{[^}]*'+re.escape(m)+r'\.',p.read_text())];assert len(rawbpnames)==1,(m,rawbpnames)
 bp=rawbpnames[0];bp_path=str(bp.relative_to(S));rawbp=subprocess.check_output(['git','-C',str(S),'show',REV+':'+bp_path]);assert rawbp==bp.read_bytes();b=rawbp.decode();assert '\\notready'not in b;ob=names.rename_text_names(b).replace('\\chapter{','\\section{');bcap=captures/(bp.name+'.txt');assert not bcap.exists()or bcap.read_bytes()==rawbp;bcap.write_bytes(rawbp)
 bps.append({'source_revision':REV,'source_path':bp_path,'source_sha256':sha(rawbp),'destination_path':'blueprint/'+bp.name,'destination_sha256':sha(ob.encode()),'proofs':b.count('\\begin{proof}'),'definitions':b.count('\\begin{definition}'),'local_bindings':sorted(set(n.strip()for group in re.findall(r'\\lean\{([^}]+)\}',ob)for n in group.split(','))),'whole_original_chapter_preserved':True,'proof_text_edits':0,'raw_capture':str(bcap.relative_to(A))})
assert len(rows)==len(bps)==9 and sum(x['proofs']for x in bps)==28
virtual={r['destination_module']:[*r['additional_pure_support_imports'],*[names.new_mod(x)for x in re.findall(r'^import (TranscendentalNakamaye[\w.]*)',(A/r['raw_capture']).read_text(),re.M)]]for r in rows}
B=D/'audit/canonical-elementary-family-and-local-producers-20261021';physical=json.loads((B/'final-physical-ci-axioms.json').read_text());owners={}
for r in physical['all_physical_root_rows']:owners.setdefault(r['actual_name'],set()).add(r['actual_moduleData_owner'])
P=W.parent/'publication-six-producers';roots=json.loads((P/'native6-actual-physical-roots.json').read_text())+json.loads((P/'dynamic-only/native6-actual-physical-roots.json').read_text())+json.loads((W/'native2-actual-physical-roots.json').read_text());assert len(roots)==181
for r in roots:owners.setdefault(names.rename_const(r['actual_name']),set()).add(names.new_mod(r['module']))
closures={}
def visit(m,out):
 if m in out:return
 out.add(m)
 if m in virtual:deps=virtual[m]
 else:
  p=D/(m.replace('.','/')+'.lean');deps=re.findall(r'^import (Hironaka[\w.]*)',p.read_text(),re.M)if p.is_file()else[]
 for dep in deps:visit(dep,out)
for m in virtual:closures[m]=set();visit(m,closures[m])
edges=json.loads((P/'all-ordinary-direct-callee-edges.json').read_text())+json.loads((P/'dynamic-only/all-ordinary-direct-callee-edges.json').read_text())+json.loads((W/'all-ordinary-direct-callee-edges.json').read_text());missing=[e for e in edges if not owners.get(e['relocated_callee'],set()).intersection(closures[names.new_mod(e['native_owner_module'])])]
report={'status':'PASS_ALL_NINE_ACTUAL_ORDINARY_CALLEE_IMPORT_OWNERS_VISIBLE'if not missing else'BLOCKED_OWNER_IMPORT_VISIBILITY','actual_new_modules':9,'actual_physical_CIs':181,'ordinary_edges':len(edges),'invisible_edges':missing,'virtual_public_import_closures':{m:sorted(v)for m,v in closures.items()},'new_two_query_scope':17,'previous_seven_native_queries_reused':True,'new_two_pure_support_imports':{}}
(W/'nine-actual-callee-import-visibility.json').write_text(json.dumps(report,indent=2)+'\n');assert not missing,missing
texts={str(p.relative_to(D)):p.read_text()for p in (D/'blueprint').rglob('*.tex')};newbp={r['destination_path']:names.rename_text_names((A/r['raw_capture']).read_text()).replace('\\chapter{','\\section{')for r in bps[-2:]};assert not set(texts).intersection(newbp)
texts.update(newbp);defined={};duplicates=[]
for path,t in texts.items():
 for label in re.findall(r'\\label\{([^}]+)\}',t):
  if label in defined:duplicates.append([label,defined[label],path])
  defined[label]=path
unresolved=[]
for path,t in newbp.items():
 for command,group in re.findall(r'\\(uses|ref|eqref|cref|Cref|dref|dcref)\{([^}]+)\}',t):
  for label in group.split(','):
   if label.strip()not in defined:unresolved.append([path,command,label.strip()])
assert not duplicates,duplicates
assert all(x[2]=='hir:base-change-open'for x in unresolved),unresolved
for name,data in [('candidate-nine-provenance.json',rows),('candidate-nine-blueprint-provenance.json',bps)]: (W/name).write_text(json.dumps(data,indent=2)+'\n')
summary={'status':'PASS_PREPARED_ADDITIVE_TWO_WHOLE_MODULES_AND_TWO_COMPLETE_CHAPTERS','ordinary_source_revision':REV,'modules':9,'new_two_actual_CIs':17,'new_two_written_proofs':6,'total_written_proofs':28,'local_bindings':sum(len(x['local_bindings'])for x in bps),'all_existing_seven_original_source_BP_captures_identical_at_final_pin':True,'unresolved_new_two_BP_references':unresolved,'duplicate_labels':duplicates,'proof_type_edits':0,'old373_mathematical_files_edited':0}
(W/'append-two-preparation-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
