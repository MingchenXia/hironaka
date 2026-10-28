from pathlib import Path
import re,json,hashlib
A=Path(__file__).resolve().parent.parent;D=A.parents[1];plan=json.loads((A/'plan.json').read_text());seen={}
def visit(p):
 p=p.resolve()
 if p in seen:return
 assert p.is_file(),str(p)
 s=p.read_text();seen[p]=s
 for name in re.findall(r'\\input\{([^}]+)\}',s):
  q=p.parent/name
  if not q.suffix:q=q.with_suffix('.tex')
  visit(q)
visit(D/'blueprint/extensions.tex')
labels={x for s in seen.values() for x in re.findall(r'\\label\{([^}]+)\}',s)}
missing=[];bindings=[];uses=0
for r in [*plan['blueprints'],*plan['documentation_pointers']]:
 p=(D/r['destination_path']).resolve();assert p in seen,str(p)
 s=seen[p]
 for group in re.findall(r'\\lean\{([^}]+)\}',s):bindings.extend(x.strip() for x in group.split(',') if x.strip())
 for group in re.findall(r'\\uses\{([^}]+)\}',s):
  for x in group.split(','):
   uses+=1
   if x.strip() not in labels:missing.append([str(p.relative_to(D)),x.strip()])
assert not missing,missing
# The final recorded index path, rather than a guessed file name, is checked through the plan above.
modules=[r['destination_module'] for r in plan.get('support_extracts',[])]+[r['destination_module'] for r in plan['source_modules']]
bindings=list(dict.fromkeys(bindings))
s='import Hironaka\n'+''.join('import '+m+'\n' for m in modules)+'import Lean\nopen Lean\nrun_cmd do\n  let env := (← getEnv).setExporting false\n  setEnv env\n  let bindings := #['+', '.join(json.dumps(b) for b in bindings)+']\n  for name in bindings do\n    unless env.contains name.toName do throwError "Missing literal binding {name}"\n  logInfo m!"ALL_LITERAL_BINDINGS {bindings.size}"\n'
(A/'independent/LiteralBindings.lean').write_text(s)
result={'status':'PASS_STATIC_INPUT_USES_CLOSURE','master_inputs':len(seen),'uses':uses,'unique_bindings':len(bindings),'missing_uses':[],'actual_input_paths':[str(p.relative_to(D)) for p in seen],'bindings':bindings,'plan_sha256':hashlib.sha256((A/'plan.json').read_bytes()).hexdigest()}
(A/'independent/doc-closure.json').write_text(json.dumps(result,indent=2)+'\n');print(len(seen),uses,len(bindings))
