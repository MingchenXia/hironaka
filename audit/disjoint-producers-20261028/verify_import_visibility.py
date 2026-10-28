#!/usr/bin/env python3
"""Offline actual ordinary-CI owner visibility; all generated raw edges retained."""
from pathlib import Path
import ast, collections, hashlib, json, re
A=Path(__file__).resolve().parent;D=A.parents[1]
plan=json.loads((A/'plan.json').read_text())
scope={'re':re}
nodes=[x for x in ast.parse((A/'sync_cohort.py').read_text()).body
       if isinstance(x,ast.FunctionDef)and x.name in ['uncomment','imports']]
exec(compile(ast.Module(body=nodes,type_ignores=[]),'cohort-import-parser','exec'),scope)
graph={str(p.relative_to(D).with_suffix('')).replace('/','.'):scope['imports'](p.read_text())
       for p in (D/'Hironaka').rglob('*.lean')}
maps={r['source_module']:r['destination_module']for r in plan['source_modules']}
selected={}
for row in plan['support_extracts']:
    for decl in row['selected_original_declarations']:
        name=re.search(r'^theorem\s+(\w+)',decl['original_text'],re.M).group(1)
        selected[row['source_module']+'.'+name]=row['destination_module']
memo={};active=set()
def closure(module):
    if module in memo:return memo[module]
    assert module not in active,('Import cycle',module)
    active.add(module);out={module}
    for dep in graph.get(module,[]):
        if dep in graph:out|=closure(dep)
    active.remove(module);memo[module]=out;return out
for module in graph:closure(module)
data=json.loads((A/'callee-preflight-attempt01/actual-callees.json').read_text())
old=collections.defaultdict(set);new=collections.defaultdict(set)
for r in data['old_public_actual_physical_roots']:old[r['actual_name']].add(r['module'])
for r in data['native_actual_physical_roots']:new[r['canonical_name']].add(maps[r['module']])
checked=0;missing=[]
def check(caller,callee,canonical):
    global checked
    owners=old[canonical]|new[canonical]
    if callee in selected:owners=owners|{selected[callee]}
    checked+=1
    if not(owners&closure(caller)):
        missing.append({'caller':caller,'native_callee':callee,'actual_owners':sorted(owners)})
for e in data['all_project_type_whole_value_edges']:
    if not e['private_or_generated_diagnostic']:
        check(maps[e['native_caller_module']],e['native_callee'],e['canonical_callee'])
support_edges=[]
for path in ['support-callee-closure/all-raw-direct-callee-edges.json',
             'pivot-support-callee-closure/all-raw-direct-callee-edges.json']:
    support_edges.extend(json.loads((A/path).read_text()))
for e in support_edges:
    if not e['project_namespace'] or e['caller_native_name']not in selected:continue
    if any(s in e['native_callee']for s in ['.eq_','.match_','._match_','._proof_',
        '._simp_','._aux_','.congr_simp','_hyg','_@','_elambda','_private.']):continue
    check(selected[e['caller_native_name']],e['native_callee'],e['relocated_ordinary_callee'])
out={'status':'PASS'if not missing else'MISSING_ORDINARY_IMPORTS',
     'ordinary_edges_checked':checked,'missing':missing,'graph_acyclic':True,
     'new_file_pure_imports':{r['destination_module']:r['additional_pure_support_imports']
         for r in plan['source_modules']if r['additional_pure_support_imports']},
     'source_graph_SHA256':hashlib.sha256(json.dumps(graph,sort_keys=True).encode()).hexdigest(),
     'actual_compiled_metadata_not_source_path_availability':True,
     'private_generated_edges_preserved_for_exhaustive_kernel_Expr_gates':True,
     'kernel_or_Expr_replay':False}
target=A/'ordinary-import-visibility-final.json';target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2));assert not missing
