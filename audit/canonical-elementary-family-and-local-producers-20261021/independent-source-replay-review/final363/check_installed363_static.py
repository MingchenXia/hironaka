"""Prepared offline; run only after the installation owner explicitly freezes363.
No Lean, kernel, Expr, build, source installer, or source mutation is invoked.
"""
from pathlib import Path
import argparse,ast,hashlib,json,re,subprocess,sys
O=Path(__file__).resolve().parent;A=O.parents[1];R=A.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--header-plan',type=Path,required=True);ap.add_argument('--installed-freeze',required=True);args=ap.parse_args()
 assert args.installed_freeze.strip(), 'An owner freeze signal is required'
 result=O/'final363-static-checks.json';assert not result.exists(),'Once-only final witness already exists'
 C=json.loads((O/'offline-review-inputs.json').read_text());P=Path(C['additive_preparation_root'])
 for name,h in C['frozen_additive_plans'].items():assert sha((P/name).read_bytes())==h,name
 fpfile=Path(C['base323_fingerprint_path']);assert sha(fpfile.read_bytes())==C['base323_fingerprint_sha256'];fp=json.loads(fpfile.read_text())
 initial=json.loads((A/'initial-port-plan.json').read_text())
 for rel,h in initial['existing_destination_math_source_digests'].items():assert sha((R/rel).read_bytes())==h,rel
 for rel,h in initial['existing_blueprint_tex_digests'].items():
  if rel!='blueprint/extensions.tex':assert sha((R/rel).read_bytes())==h,rel
 for rel,h in initial['toolchain_profiles'].items():assert sha((R/rel).read_bytes())==h,rel
 for row in C['base323_source_identities']:assert sha((R/row['destination_path']).read_bytes())==fp[row['destination_path']],row['destination_path']
 M=json.loads((P/'module-provenance-plan.json').read_text());B=json.loads((P/'blueprint-provenance-plan.json').read_text());assert len(M)==len(B)==40
 header=json.loads(args.header_plan.read_text());rows=header['files']if isinstance(header,dict)else header
 assert len(rows)==8 and sum(len(r['commands'])for r in rows)==9
 by_header={r.get('module',r.get('destination_module')):r for r in rows};assert len(by_header)==8
 notation={r['destination_module']for r in json.loads((P/'seven-notation-source-generation-initial.json').read_text())['parents']};assert not notation.intersection(by_header)
 sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'scripts'))
 import upstream_namespace_map as names
 names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
 frozen=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'),env);relocate=env['relocate']
 tree=ast.parse((P/'frozen-inputs/sync_frozen_sources.py').read_text());HEADER=ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='HEADER'for t in n.targets)))
 source_checks=[]
 for row in M:
  assert row['published_source_revision']==C['fixed_additive_revision']
  raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',C['fixed_additive_revision']+':'+row['source_path']]);assert sha(raw)==row['source_sha256'];assert(P/'original'/row['source_path']).read_bytes()==raw
  text=HEADER+relocate(raw.decode());assert sha(text.encode())==row['destination_sha256'];assert(P/row['candidate_path']).read_bytes()==text.encode()
  commands=by_header.get(row['destination_module'],{}).get('commands',[])
  first=re.search(r'^\s*(?:(?:private|noncomputable|local)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|axiom|opaque)\b',text,re.M)
  for cmd in commands:
   assert text.count(cmd['before'])==1 and first and text.index(cmd['before'])<first.start(),(row['destination_module'],cmd)
   assert cmd['before'].startswith('open ')and cmd['after'].startswith('open _root_.'),cmd
   text=text.replace(cmd['before'],cmd['after'],1)
  actual=(R/row['destination_path']).read_bytes();assert text.encode()==actual,row['destination_path']
  source_checks.append({'path':row['destination_path'],'fixed_source_sha256':row['source_sha256'],'installed_sha256':sha(actual),'header_qualifications':commands,'entire_remaining_original_source_payload_preserved':True})
 assert set(by_header)<={r['destination_module']for r in M}
 proof_count=0
 for row in B:
  raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',C['fixed_additive_revision']+':'+row['source_path']]);assert sha(raw)==row['source_sha256'];assert(P/'original'/row['source_path']).read_bytes()==raw
  candidate=(P/row['candidate_path']).read_bytes();assert sha(candidate)==row['destination_sha256'];assert(R/row['destination_path']).read_bytes()==candidate,row['destination_path']
  before=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',raw.decode(),re.S);after=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',candidate.decode(),re.S);assert len(before)==len(after)==row['proofs'];assert all(names.rename_text_names(x)==y for x,y in zip(before,after));proof_count+=len(before)
 assert proof_count==122 and sum(r['definitions']for r in B)==3
 # Exactly one base source-facing BP attachment correction; all math text unchanged.
 exception=C['base_BP_metadata_exception'];basecapture=A/'full325-candidate-frozen-before-export323/candidate-files'
 for rel in C['base309_BP_paths']:
  before=(basecapture/rel).read_text();assert sha(before.encode())==fp[rel]
  expected=before
  if rel==exception['path']:
   i=before.index('\\label{'+exception['label']+'}');lo=before.rfind('\\begin{lemma}',0,i);hi=before.index('\\end{proof}',i)+len('\\end{proof}')
   node=before[lo:hi];assert node.count(exception['old_attachment'])==1 and node.count('\\leanok')==2
   node=node.replace(exception['old_attachment'],exception['new_attachment'],1).replace('\\leanok','\\mixedleanok');expected=before[:lo]+node+before[hi:]
  assert(R/rel).read_bytes()==expected.encode(),rel
 def remove_exact_block(current,block,baseline):
  for candidate in [block,block+'\n','\n'+block]:
   if current.count(candidate)==1 and current.replace(candidate,'',1)==baseline:return candidate
  raise AssertionError('Umbrella/master does not preserve its exact base plus the declared block')
 roots=(P/'candidate-root-imports.txt').read_text();assert len(re.findall(r'^import ',roots,re.M))==40
 masterblock=(P/'candidate-blueprint-inputs.txt').read_text();assert len(re.findall(r'^\\input\{',masterblock,re.M))==40
 root=(R/'Hironaka.lean').read_text();master=(R/'blueprint/extensions.tex').read_text()
 rootdelta=remove_exact_block(root,roots,(O/'base323-Hironaka.lean').read_text());masterdelta=remove_exact_block(master,masterblock,(O/'base323-extensions.tex').read_text());assert len(re.findall(r'\\input\{',master))==969
 all_BP=C['base309_BP_paths']+[r['destination_path']for r in B];assert len(all_BP)==len(set(all_BP))==349
 assert sum((R/p).read_text().count('\\begin{proof}')for p in all_BP)==1110
 upstream={v.strip()for p in all_BP for g in re.findall(r'\\upstreamlean\{([^}]+)\}',(R/p).read_text())for v in g.split(',')};assert upstream==set(C['upstream_only_public_to_native'].values())and len(upstream)==14
 part=json.loads((A/'deferred-complete-module-partition.json').read_text());deferred={r['module']for r in part['deferred_complete_modules']};assert deferred=={'Hironaka.Resolution.HironakaOriginalGlobalOffZero','Hironaka.Resolution.HironakaOriginalGlobalProperModification'}
 labels=set()
 for r in part['deferred_complete_modules']+part['deferred_complete_blueprint_chapters']:
  assert not(R/r['destination_path']).exists();raw=(A/r['canonical_draft_capture']).read_bytes();assert sha(raw)==r['sha256']
  if r['destination_path'].endswith('.tex'):labels.update(re.findall(r'\\label\{([^}]+)\}',raw.decode()))
 assert len(labels)==7
 physical={str(p.relative_to(R))for p in(R/'Hironaka').rglob('*.lean')}|{'Hironaka.lean'};expected=set(initial['existing_destination_math_source_digests'])|{r['destination_path']for r in C['base323_source_identities']}|{r['destination_path']for r in M}|{'Hironaka.lean'};assert physical==expected and len(physical)==1523
 imports={p.removesuffix('.lean').replace('/','.'):re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',(R/p).read_text(),re.M)for p in physical};assert not any(deferred.intersection(v)for v in imports.values())
 seen=set()
 def visit(m):
  if m in seen:return
  assert m in imports,m
  seen.add(m)
  for d in imports[m]:
   if d=='Hironaka'or d.startswith('Hironaka.'):visit(d)
 visit('Hironaka');assert seen==set(imports)
 for p in all_BP:
  refs={v.strip()for g in re.findall(r'\\(?:uses|ref|eqref)\{([^}]+)\}',(R/p).read_text())for v in g.split(',')};assert not refs.intersection(labels),p
 out={'status':'PASS_FINAL363_INSTALLED_STATIC_SOURCE_BP_AND_PRESERVATION','freeze_label':args.installed_freeze,'base_revision':C['fixed_base_revision'],'additive_revision':C['fixed_additive_revision'],'base_sources_preserved':323,'additive_whole_source_modules':40,'total_new_source_records':363,'old_sources_preserved':1159,'old_BP_preserved':619,'frozen_profiles_preserved':4,'header_only_qualifications':9,'qualified_additive_files':8,'notation_owner_sources_context_unchanged':7,'new_source_checks':source_checks,'source_facing_BP_chapters':349,'entire_written_proofs':1110,'additive_entire_written_proofs':122,'additive_definition_nodes':3,'upstream_only_original_names':sorted(upstream),'base_BP_metadata_exception':exception,'deferred_whole_modules':sorted(deferred),'deferred_whole_chapters':2,'deferred_proofs':7,'deferred_bindings':11,'physical_and_reachable_Lean_modules_including_root':1523,'master_inputs':969,'exact_added_root_block':rootdelta,'exact_added_master_block':masterdelta,'source_or_proof_payload_edits':0,'within_module_root_filtering':False,'Lean_kernel_Expr_runtime_invocations':0,'publication_runtime_completion_claimed':False}
 result.write_text(json.dumps(out,indent=2)+'\n');print(result);print(sha(result.read_bytes()))
if __name__=='__main__':main()
