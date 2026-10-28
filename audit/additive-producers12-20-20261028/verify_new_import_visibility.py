#!/usr/bin/env python3
"""Check actual ordinary CI owners against each new module's source imports."""
from pathlib import Path
import ast
import collections
import hashlib
import json
import re

E = Path(__file__).resolve().parent
D = E.parents[1]
A = D / 'audit/disjoint-producers-20261028'
plan = json.loads((E / 'installation-plan.json').read_text())
scope = {'re': re}
nodes = [node for node in ast.parse((A / 'sync_cohort.py').read_text()).body if isinstance(node, ast.FunctionDef) and node.name in ['uncomment', 'imports']]
exec(compile(ast.Module(body=nodes, type_ignores=[]), 'new-import-parser', 'exec'), scope)
graph = {str(path.relative_to(D).with_suffix('')).replace('/', '.'): scope['imports'](path.read_text()) for path in (D / 'Hironaka').rglob('*.lean')}
memo = {}
active = set()
def closure(module):
    if module in memo:
        return memo[module]
    assert module not in active, ('Import cycle', module)
    active.add(module)
    result = {module}
    for dep in graph.get(module, []):
        if dep in graph:
            result |= closure(dep)
    active.remove(module)
    memo[module] = result
    return result
for module in graph:
    closure(module)

maps = {row['source_module']: row['destination_module'] for row in plan['source_modules']}
selected = {}
for row in plan['support_extracts']:
    for declaration in row['selected_original_declarations']:
        selected[declaration['original_name']] = row['destination_module']
meta = json.loads((E / 'callee-preflight-attempt01/actual-callees.json').read_text())
old = collections.defaultdict(set)
new = collections.defaultdict(set)
for row in meta['old_public_actual_physical_roots']:
    old[row['actual_name']].add(row['module'])
for row in meta['native_actual_physical_roots']:
    new[row['canonical_name']].add(maps[row['module']])
checked = 0
missing = []
def check(caller, native_callee, canonical):
    global checked
    owners = old[canonical] | new[canonical]
    if native_callee in selected:
        owners |= {selected[native_callee]}
    checked += 1
    if not owners & closure(caller):
        missing.append({'caller': caller, 'native_callee': native_callee, 'canonical_callee': canonical, 'actual_owners': sorted(owners)})
for edge in meta['all_project_type_whole_value_edges']:
    if not edge['private_or_generated_diagnostic']:
        check(maps[edge['native_caller_module']], edge['native_callee'], edge['canonical_callee'])
for edge in json.loads((E / 'support-callee-closure/all-raw-direct-callee-edges.json').read_text()):
    if edge['project_namespace'] and edge['caller_native_name'] in selected:
        check(selected[edge['caller_native_name']], edge['native_callee'], edge['relocated_ordinary_callee'])
result = {
    'status': 'PASS_ACTUAL_ORDINARY_OWNER_IMPORT_VISIBILITY' if not missing else 'MISSING_ACTUAL_ORDINARY_IMPORTS',
    'ordinary_edges_checked': checked, 'missing': missing, 'source_graph_acyclic': True,
    'source_graph_sha256': hashlib.sha256(json.dumps(graph, sort_keys=True).encode()).hexdigest(),
    'new_pure_support_imports': {row['destination_module']: row['additional_pure_support_imports'] for row in plan['source_modules'] + plan['support_extracts'] if row['additional_pure_support_imports']},
    'metadata_is_actual_compiled_CI_owner_data': True,
    'formal_kernel_Expr_or_physical_audits_filter_roots': False,
    'compiler_used': False,
}
target = E / 'ordinary-import-visibility-final.json'
assert not target.exists()
target.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
assert not missing
