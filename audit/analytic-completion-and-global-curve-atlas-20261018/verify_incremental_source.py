"""Read-only full original source/blueprint replay for the frozen313 public increment.

Only normal published Git is required. No private Horizon ledger or Lean run is used.
"""
from pathlib import Path
import argparse,ast,hashlib,json,re,subprocess,sys
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source-root',type=Path,required=True)
p.add_argument('--revision',default='7266ce19c9d3f79a8693f7ded964755af7af59a7');a=p.parse_args()
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BASE='7077e5469e0d6a5ce3a95e51b5e7400dc2d906ec'
sha=lambda b:hashlib.sha256(b).hexdigest();load=lambda n:json.loads((HERE/n).read_text())
assert a.revision=='7266ce19c9d3f79a8693f7ded964755af7af59a7'
show=lambda path:subprocess.check_output(['git','-C',str(a.source_root),'show',a.revision+':'+path])
sys.path.insert(0,str(ROOT/'scripts'));import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['','2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'))
for rec in load('frozen-tool-profiles.json'):
 assert sha((ROOT/rec['path']).read_bytes())==rec['sha256'],rec['path']
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
whole=load('provenance.json');plan=load('frozen-extraction-plan.json');accepted=load('accepted-native-33-source-records.json')
assert len(whole)==33 and {r['source_module'] for r in whole}==set(plan['modules'])
for rec in whole:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_sha256']
 assert sha(raw)==next(r['sha256'] for r in accepted if r['module']==rec['source_module'])
 out=header+relocate(raw.decode());assert sha(out.encode())==rec['initial_synchronized_destination_sha256']
 for change in rec['administrative_elaboration_contexts']:
  assert out.count(change['before'])==1;out=out.replace(change['before'],change['after'])
 first=re.search(r'^import ',out,re.M);assert first
 out=out[:first.start()]+''.join('import '+m+'\n' for m in rec['additional_pure_support_imports'])+out[first.start():]
 actual=(ROOT/(rec['destination_module'].replace('.','/')+'.lean')).read_bytes()
 assert actual==out.encode() and sha(actual)==rec['destination_sha256'],rec['destination_module']
supports=load('new-support-provenance.json') if (HERE/'new-support-provenance.json').exists() else []
contexts=load('original-support-contexts.json') if (HERE/'original-support-contexts.json').exists() else []
for rec in supports:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_parent_sha256'];lines=raw.decode().splitlines(keepends=True)
 sl,sc,el,ec=rec['compiler_source_range'];block=lines[sl][sc:]+''.join(lines[sl+1:el])+lines[el][:ec] if sl!=el else lines[sl][sc:ec]
 assert raw.count(block.encode())==1 and sha(block.encode())==rec['source_complete_declaration_sha256']
 assert (HERE/rec['source_complete_declaration_file']).read_text()==block
 actual=(ROOT/rec['destination_path']).read_bytes();assert sha(actual)==rec['destination_sha256']
 assert actual.count(relocate(block).encode())==1
for ctx in contexts:
 selected=[r for r in supports if r['destination_module']==ctx['destination_module']]
 raw=show(selected[0]['source_path']).decode();lines=raw.splitlines(keepends=True)
 last=max(r['compiler_source_range'] for r in selected);_,_,el,ec=last
 prefix=''.join(lines[:el])+lines[el][:ec]
 assert prefix==ctx['original_complete_prefix_through_selected_third_declaration']
 assert not ctx['omitted_original_imports_or_opens'] and ctx['omitted_original_proof_tokens']==0
 for scope in ctx['original_closing_scope_pieces']:assert raw.count(scope)==1
 for between in ctx['original_inter_declaration_contexts']:assert between in raw
 out='/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/\n'
 out+=''.join('import '+m+'\n' for m in ctx['pure_existing_imports'])+relocate(prefix)+'\n\n'
 out+=''.join(relocate(s) for s in ctx['original_closing_scope_pieces'])
 assert out==(ROOT/ctx['destination_path']).read_text()
external=json.loads((ROOT/'scripts/upstream_blueprint_external_bindings.json').read_text())
unbound=json.loads((ROOT/'scripts/upstream_blueprint_unbound_bindings.json').read_text())
typography=json.loads((ROOT/'scripts/upstream_blueprint_typography.json').read_text());bps=load('blueprint-provenance.json')
for bp in bps:
 raw=show(bp['source_path']);assert sha(raw)==bp['source_sha256']
 out=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
 for change in typography.get(Path(bp['destination_path']).name,[]):
  assert out.count(change['before'])==1;out=out.replace(change['before'],change['after'])
 out=annotate(out,external,unbound);actual=(ROOT/bp['destination_path']).read_bytes()
 assert actual==out.encode() and sha(actual)==bp['destination_sha256']
 assert out.count('\\begin{proof}')==raw.decode().count('\\begin{proof}')==bp['proofs']
 assert all(t.strip() for t in re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',out))
old=subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-r','--name-only',BASE,'--','Hironaka'],text=True).splitlines()
old=[f for f in old if f.endswith('.lean')];assert len(old)==968
for f in old:
 before=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+f]);assert (ROOT/f).read_bytes()==before,f
oldroot=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':Hironaka.lean'],text=True);mark=oldroot.find('/-!');assert mark>=0
assert (ROOT/'Hironaka.lean').read_text()==oldroot[:mark]+''.join('import '+names.new_mod(m)+'\n\n' for m in plan['leaf_roots'])+oldroot[mark:]
oldmain=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':blueprint/extensions.tex'],text=True);needle='\\begin{thebibliography}{99}'
expected=oldmain.replace(needle,''.join('\\input{'+Path(bp['destination_path']).stem+'}\n' for bp in bps)+needle)
for change in load('master-documentation-contexts.json') if (HERE/'master-documentation-contexts.json').exists() else []:
 assert expected.count(change['before'])==1;expected=expected.replace(change['before'],change['after'])
assert (ROOT/'blueprint/extensions.tex').read_text()==expected
bindings=load('new-local-bindings.json');assert len(bindings)==175 and set(bindings)=={b for bp in bps for b in bp['local_bindings']}
targets=load('new-module-targets.json');assert targets==[r['destination_module'] for r in whole]+list(dict.fromkeys(r['destination_module'] for r in supports))
assert len(targets)==len(set(targets))
r={'status':'PASS_COMPLETE_NORMAL_PUBLISHED_SOURCE_REPLAY_AND_968_PREVIOUS_SOURCE_GUARD',
 'accepted_native_checkpoint':plan['checkpoint'],'normal_published_revision':a.revision,'previous_public_main':BASE,
 'previous_mathematical_sources_byte_identical':len(old),'whole_original_modules':len(whole),
 'original_pure_support_modules':len(contexts),'complete_original_support_declarations':len(supports),
 'complete_blueprint_chapters':len(bps),'complete_original_blueprint_proofs':sum(bp['proofs'] for bp in bps),
 'local_blueprint_bindings':len(bindings),'new_module_targets':len(targets),'root_changes_only_recorded_imports':len(plan['leaf_roots']),
 'private_ledger_required':False,'original_type_proof_text_changes':0,'frozen_tool_profiles_unchanged':True,
 'limitation':'Source replay only. Complete compiled root, whole-expression, axiom and frozen kernel gates remain separate.'}
(HERE/'published-source-replay.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
