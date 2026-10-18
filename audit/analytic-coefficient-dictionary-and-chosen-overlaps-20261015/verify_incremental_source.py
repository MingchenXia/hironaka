"""Read-only complete source replay for the bounded dependency recovery.

This checks text and frozen provenance only. It does not replace the later
independent entire-expression, kernel, or blueprint semantic audits.
"""
from pathlib import Path
import argparse, ast, hashlib, json, re, subprocess, sys

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source-root',type=Path,required=True)
p.add_argument('--revision',default='09dc511c4a14836a0287748d1a63f9f467f677d3')
a=p.parse_args()
here=Path(__file__).resolve().parent
dest=here.parents[1]
sys.path.insert(0,str(dest/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
relocation_source=dest/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
relocation=next(n for n in ast.parse(relocation_source.read_text()).body
                if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[relocation],type_ignores=[]),str(relocation_source),'exec'))
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda name:json.loads((here/name).read_text())
def show(path):
    return subprocess.check_output(['git','-C',str(a.source_root),'show',a.revision+':'+path])

assert re.fullmatch('[0-9a-f]{40}',a.revision)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
whole=load('provenance.json')
imports=load('additional-pure-support-imports.json')
for rec in whole:
    raw=show(rec['source_path'])
    assert sha(raw)==rec['source_sha256'],rec['source_path']
    output=header+relocate(raw.decode())
    assert sha(output.encode())==rec['initial_synchronized_destination_sha256']
    for change in rec['administrative_elaboration_contexts']:
        assert output.count(change['before'])==1
        output=output.replace(change['before'],change['after'])
    extras=rec['additional_pure_support_imports']
    assert extras==imports.get(rec['destination_module'],[])
    for m in extras:assert (dest/(m.replace('.','/')+'.lean')).is_file(),m
    first=re.search(r'^import ',output,re.M)
    output=output[:first.start()]+''.join('import '+m+'\n' for m in extras)+output[first.start():]
    actual=(dest/(rec['destination_module'].replace('.','/')+'.lean')).read_bytes()
    assert actual==output.encode() and sha(actual)==rec['destination_sha256'],rec['destination_module']

supports=load('new-support-provenance.json')
contexts=load('original-support-contexts.json')
for rec in supports:
    raw=show(rec['source_path'])
    assert sha(raw)==rec['source_parent_sha256'],rec['source_module']
    body=(here/rec['source_complete_declaration_file']).read_bytes()
    assert sha(body)==rec['source_complete_declaration_sha256'] and raw.count(body)==1
    lines=raw.decode().splitlines(keepends=True)
    sl,sc,el,ec=rec['compiler_source_range']
    fragment=(lines[sl][sc:]+''.join(lines[sl+1:el])+lines[el][:ec]
              if sl!=el else lines[sl][sc:ec])
    assert fragment.encode()==body,rec['actual_original_declaration']
    actual=(dest/rec['destination_path']).read_bytes()
    assert sha(actual)==rec['destination_sha256']
    assert actual.count(relocate(body.decode()).encode())==1
for ctx in contexts:
    matching=[r for r in supports if r['destination_module']==ctx['destination_module']]
    assert matching
    raw=show(matching[0]['source_path']).decode()
    first=ctx['compiler_first_declaration_start_line']
    assert ''.join(raw.splitlines(keepends=True)[:first])==ctx['source_original_initial_prelude']
    selected=ctx['source_original_initial_prelude']
    mode=ctx['original_context_selection_mode']
    if mode and mode not in ('contiguous','strict_density_context','analytic_component_context',
                             'irreducible_nonempty_context'):
        selected=raw[:raw.index(mode)]
    for change in ctx['administrative_context_adjustments']:
        assert selected.count(change['before'])==1
        selected=selected.replace(change['before'],change['after'],1)
        if mode in ('analytic_component_context','irreducible_nonempty_context'):
            # Every retained scope command and variable line is itself original;
            # this is a selection of original context, not an invented hypothesis.
            for line in change['after'].splitlines(keepends=True):
                assert line in raw,(ctx['source_module'],line)
    selected=re.sub(r'\nomit [^\n]+\bin\n\s*$','\n',selected)
    selected=re.sub(r'\nvariable [^\n]+\bin\n\s*$','\n',selected)
    selected+=''.join(ctx['appended_original_contexts'])
    assert selected==ctx['original_prelude'],ctx['destination_module']
    for extra in ctx['appended_original_contexts']:assert extra in raw
    for block in ctx['original_declaration_blocks']:assert raw.count(block)==1
    for change in ctx['administrative_context_adjustments']:
        assert raw.count(change['before'])==1
    output='/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/\n'
    output+=''.join('import '+m+'\n' for m in ctx['pure_support_imports'])
    output+=''.join('import '+m+'\n' for m in ctx['unchanged_parent_imports'])
    output+=relocate(ctx['original_prelude']).replace('Hironaka.NonKahlerLocus','Hironaka')+'\n'
    output+='\n\n'.join(relocate(b) for b in ctx['original_declaration_blocks'])+'\n\n'
    output+=''.join(relocate('end'+(' '+n if n else '')+'\n').replace('Hironaka.NonKahlerLocus','Hironaka')
                    for n in ctx['closing_scopes'])
    actual=(dest/matching[0]['destination_path']).read_text()
    assert output==actual,ctx['destination_module']

reused=load('reused-existing-support-provenance.json')
for rec in reused:
    raw=show(rec['source_path'])
    assert sha(raw)==rec['source_parent_sha256'],rec['source_module']
    lines=raw.decode().splitlines(keepends=True)
    sl,sc,el,ec=rec['compiler_source_range']
    fragment=(lines[sl][sc:]+''.join(lines[sl+1:el])+lines[el][:ec]
              if sl!=el else lines[sl][sc:ec])
    body=(here/rec['source_complete_declaration_file']).read_bytes()
    assert fragment.encode()==body and sha(body)==rec['source_complete_declaration_sha256']
    omitted=rec['existing_public_omitted_original_documentation']
    if omitted:
        assert re.fullmatch(r'/--[\s\S]*?-/\n',omitted)
        assert fragment.startswith(omitted)
        fragment=fragment[len(omitted):]
    actual=(dest/rec['destination_path']).read_bytes()
    assert sha(actual)==rec['destination_sha256'],rec['destination_module']
    assert actual.count(relocate(fragment).encode())==1,rec['actual_original_declaration']

external=json.loads((dest/'scripts/upstream_blueprint_external_bindings.json').read_text())
unbound=json.loads((dest/'scripts/upstream_blueprint_unbound_bindings.json').read_text())
typography=json.loads((dest/'scripts/upstream_blueprint_typography.json').read_text())
bps=load('blueprint-provenance.json')
for bp in bps:
    raw=show(bp['source_path'])
    assert sha(raw)==bp['source_sha256'],bp['source_path']
    output=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
    for change in typography.get(Path(bp['destination_path']).name,[]):
        assert output.count(change['before'])==1
        output=output.replace(change['before'],change['after'])
    output=annotate(output,external,unbound)
    actual=(dest/bp['destination_path']).read_bytes()
    assert actual==output.encode() and sha(actual)==bp['destination_sha256'],bp['destination_path']

base='3aa1692af186967f63d4197a34114d6e316aed95'
old=subprocess.check_output(['git','-C',str(dest),'ls-tree','-r','--name-only',base,'--','Hironaka']).decode().splitlines()
old=[f for f in old if f.endswith('.lean')]
repair=load('original-cstar-prerequisite-context-repair.json')
assert repair['path']=='Hironaka/Analytic/GeometricPureDimension.lean'
assert repair['before_sha256']=='7aebcdf504092ad9329a96cc0947da21d89d6be4e8f87eb9780d8261022661fc'
assert repair['after_sha256']=='ba36797787bd4c4ae7ba72ba6649a2c48cae1dc0ce93df9eef31b3d32095228b'
assert repair['before']=='import Hironaka.Analytic.ComplexAnalyticSubvarieties\n'
assert repair['after']==repair['before']+'import Mathlib.Analysis.CStarAlgebra.Classes\n'
unchanged_old=[];repaired_old=[]
for f in old:
    before=subprocess.check_output(['git','-C',str(dest),'show',base+':'+f])
    actual=(dest/f).read_bytes()
    if f==repair['path']:
        assert sha(before)==repair['before_sha256'] and sha(actual)==repair['after_sha256']
        assert before.count(repair['before'].encode())==1
        assert actual==before.replace(repair['before'].encode(),repair['after'].encode(),1)
        repaired_old.append(f)
    else:
        assert actual==before,f
        unchanged_old.append(f)
assert len(old)==887 and len(unchanged_old)==886 and repaired_old==[repair['path']]
roots=load('root-source-modules.json')
oldroot=subprocess.check_output(['git','-C',str(dest),'show',base+':Hironaka.lean']).decode()
newroot=(dest/'Hironaka.lean').read_text()
added=['import '+r['destination_module'] for r in whole if r['source_module'] in roots]
assert len(added)==len(roots)==14
for line in added:
    assert newroot.count(line+'\n')==1
    newroot=newroot.replace(line+'\n\n','',1)
assert newroot==oldroot,'Root changed beyond the fourteen recorded imports'
bindings=load('new-local-bindings.json')
assert len(bindings)==541,len(bindings)
targets=load('new-module-targets.json')
expected=[r['destination_module'] for r in whole]+list(dict.fromkeys(r['destination_module'] for r in supports))
assert targets==expected and len(targets)==len(set(targets))
receipt={'status':'PASS_COMPLETE_SOURCE_TEXT_REPLAY_AND_OLD_SOURCE_GUARD',
  'published_native_revision':a.revision,'native_frozen_revision':'db4e4065403b4ab8b077fac41985825931e5cc02',
  'whole_new_modules':len(whole),'new_pure_support_modules':len(contexts),
  'complete_original_support_declarations':len(supports),'complete_new_blueprints':len(bps),
  'reused_existing_complete_original_support_declarations':len(reused),
  'complete_original_blueprint_proofs':sum(x['proofs'] for x in bps),
  'old_mathematical_modules_byte_identical':len(unchanged_old),
  'previous_source_exact_original_instance_import_repairs':repaired_old,
  'previous_source_repair_changes_declaration_or_proof_tokens':False,
  'affected_previous_module_kernel_replay_required':True,
  'new_module_targets':len(targets),
  'root_changes_only_recorded_imports':len(added),
  'exact_local_bindings_unchanged':len(bindings),
  'limitation':'Textual provenance replay only; independent entire type/value, kernel and blueprint semantic checks remain separate.'}
(here/'source-recovery-replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
