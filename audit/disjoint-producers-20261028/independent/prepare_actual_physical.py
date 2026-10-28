from pathlib import Path
import json,re
A=Path(__file__).resolve().parent.parent
plan=json.loads((A/'plan.json').read_text())
modules=[r['destination_module'] for r in plan.get('support_extracts',[])]+[r['destination_module'] for r in plan['source_modules']]
assert len(modules)==len(set(modules))
bindings=[]
for row in [*plan['blueprints'],*plan['documentation_pointers']]:
    s=(A.parents[1]/row['destination_path']).read_text()
    for group in re.findall(r'\\lean\{([^}]+)\}',s):
        bindings.extend(x.strip() for x in group.split(',') if x.strip())
bindings=list(dict.fromkeys(bindings))
template=Path('/workspace/hironaka-current-20261025/work/hironaka-disjoint-20261028/independent-g1-controlled-split/ActualPhysicalRoots.lean').read_text()
start=template.index('  let allowed :=')
end=template.index('  let out :=')
body=template[start:end]
body=body.replace('(\"own_type_callees\",toJson ci.type.getUsedConstants.size),', '(\"own_type_callees\",toJson ci.type.getUsedConstants.size),(\"type_callee_names\",toJson (ci.type.getUsedConstants.map Name.toString)),')
body=body.replace('(\"own_value_callees\",toJson ((value.map Expr.getUsedConstants).getD #[]).size)', '(\"own_value_callees\",toJson ((value.map Expr.getUsedConstants).getD #[]).size),(\"value_callee_names\",toJson (((value.map Expr.getUsedConstants).getD #[]).map Name.toString))')
# Reuse reviewed audit algorithm, with one actual owner at a time per invocation.
for i,m in enumerate(modules):
    prefix='import '+m+'\nimport Lean.Util.CollectAxioms\n\nopen Lean\nrun_cmd do\n  let env := (← getEnv).setExporting false\n  setEnv env\n'
    prefix+='  let bindings := #['+', '.join(json.dumps(b) for b in bindings)+']\n'
    prefix+='  for binding in bindings do\n    unless env.contains binding.toName do throwError "Missing literal binding {binding}"\n'
    # Cohort bindings are checked separately with root umbrella import, avoiding unrelated missing imports.
    prefix=prefix[:prefix.index('  let bindings :=')]
    prefix+='  let target := `'+m+'\n  let some idx := env.header.moduleNames.findIdx? (· == target)\n    | throwError "Missing actual module {target}"\n  let roots := env.header.moduleData[idx]!.constants\n'
    out=A/'independent'/f'physical-{i:02d}.json'
    suffix='  let out := '+json.dumps(str(out))+'\n  IO.FS.writeFile out ((Json.mkObj [("module",toJson target.toString),\n    ("actual_root_count",toJson roots.size),("roots",Json.arr rows)]).pretty)\n  logInfo m!"ALL_ACTUAL_PHYSICAL_ROOTS {roots.size} allowed axioms only"\n'
    (A/'independent'/f'physical-{i:02d}.lean').write_text(prefix+body+suffix)
(A/'independent/modules.json').write_text(json.dumps(modules,indent=2)+'\n')
(A/'independent/literal-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
print(len(modules),len(bindings))
