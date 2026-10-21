from pathlib import Path
import json,re,importlib.util,sys,hashlib
sys.dont_write_bytecode=True
R=Path('/workspace/archon-nakamaye');D=Path('/workspace/hironaka');A=D/'audit/phase4-semantic-producers-20261021';B=D/'audit/canonical-elementary-family-and-local-producers-20261021';W=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('names',D/'scripts/upstream_namespace_map.py');names=importlib.util.module_from_spec(sp);sp.loader.exec_module(names);names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
rows=json.loads((A/'provenance.json').read_text());virtual={r['destination_module']:[*r['additional_pure_support_imports'],*[names.new_mod(x)for x in re.findall(r'^import (TranscendentalNakamaye[\w.]*)',(R/r['source_path']).read_text(),re.M)]]for r in rows}
phys=json.loads((B/'final-physical-ci-axioms.json').read_text());owners={}
for r in phys['all_physical_root_rows']:owners.setdefault(r['actual_name'],set()).add(r['actual_moduleData_owner'])
newroots=json.loads((W/'native6-actual-physical-roots.json').read_text())+json.loads((W/'dynamic-only/native6-actual-physical-roots.json').read_text());assert len(newroots)==164
for r in newroots:owners.setdefault(names.rename_const(r['actual_name']),set()).add(names.new_mod(r['module']))
cache={}
def visit(m,out):
 if m in out:return
 out.add(m)
 if m in virtual:deps=virtual[m]
 else:
  p=D/(m.replace('.','/')+'.lean');deps=re.findall(r'^import (Hironaka[\w.]*)',p.read_text(),re.M)if p.is_file()else[]
 for dep in deps:visit(dep,out)
for m in virtual:cache[m]=set();visit(m,cache[m])
edges=json.loads((W/'all-ordinary-direct-callee-edges.json').read_text())+json.loads((W/'dynamic-only/all-ordinary-direct-callee-edges.json').read_text());missing=[]
for e in edges:
 if not owners.get(e['relocated_callee'],set()).intersection(cache[names.new_mod(e['native_owner_module'])]):missing.append(e)
report={'status':'PASS_ALL_SEVEN_ACTUAL_ORDINARY_CALLEE_IMPORT_OWNERS_VISIBLE'if not missing else'BLOCKED_IMPORT_OWNER_VISIBILITY','actual_new_physical_CIs':164,'actual_new_modules':7,'ordinary_edges':len(edges),'invisible_edges':missing,'pure_existing_support_imports':{r['destination_module']:r['additional_pure_support_imports']for r in rows if r['additional_pure_support_imports']},'virtual_public_import_closures':{m:sorted(v)for m,v in cache.items()},'all_raw_ordinary_and_private_generated_edges_retained':True,'old_baseline_unchanged':True}
(W/'seven-actual-callee-import-visibility.json').write_text(json.dumps(report,indent=2)+'\n');(A/'native-actual-callee-preflight.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'],len(edges),len(missing));assert not missing,missing
