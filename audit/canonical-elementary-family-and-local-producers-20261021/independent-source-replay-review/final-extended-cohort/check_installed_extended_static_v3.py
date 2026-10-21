"""Prepared offline. Execute only after the production owner's final source/BP freeze.
Independent source/context/whole-proof checks plus a guarded source-only no-op.
Never invokes Lean, lake, native kernel, Expr, or an installation write.
"""
from pathlib import Path
import argparse, ast, contextlib, hashlib, io, json, re, runpy, subprocess, sys
sys.dont_write_bytecode=True
O=Path(__file__).resolve().parent;A=O.parents[1];R=A.parents[1]
BASE='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07';ADD='47cef49895832e3bfe492f66e1f2ac68785187dd'
sha=lambda b:hashlib.sha256(b.encode()if isinstance(b,str)else b).hexdigest()
def load(p):return json.loads(p.read_text())
def original(rev,p):return subprocess.check_output(['git','-C','/workspace/archon-publish','show',rev+':'+p])
def fingerprint(paths):return {str(p):sha(p.read_bytes())for p in sorted(set(paths))}
def strip_comments(s):
 out=[];depth=0;i=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2;continue
  if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
  if depth:out.append('\n'if s[i]=='\n'else' ');i+=1;continue
  if s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s)if j<0 else j;continue
  out.append(s[i]);i+=1
 assert not depth
 return ''.join(out)
def block(s,label):
 pos=s.index('\\label{'+label+'}');heads=list(re.finditer(r'\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\}',s[:pos]));assert heads,label
 start=heads[-1].start();kind=re.match(r'\\begin\{([^}]+)\}',s[start:])[1];end=s.index('\\end{'+kind+'}',pos)+len('\\end{'+kind+'}')
 next_node=re.search(r'\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\}',s[end:]);next_at=len(s)if next_node is None else end+next_node.start();proof=s.find('\\begin{proof}',end)
 if 0<=proof<next_at:end=s.index('\\end{proof}',proof)+len('\\end{proof}')
 return s[start:end]
def strip_attachments(s):
 s=re.sub(r'\\(?:lean|upstreamlean|upstreamunbound)\{[^{}]*\}','',s)
 return re.sub(r'\\(?:leanok|mixedleanok|historicalleanok|upstreamleanok)\b','',s)
def bindings(s,kind):return [v.strip()for g in re.findall(r'\\'+kind+r'\{([^}]+)\}',s)for v in g.split(',')]
def scope_balance(s):
 stack=[]
 for line in strip_comments(s).splitlines():
  line=line.strip();m=re.fullmatch(r'(namespace|section)\s*(\S+)?',line)
  if line=='noncomputable section':stack.append(None)
  elif m:stack.append(m[2])
  elif re.fullmatch(r'end(?:\s+\S+)?',line):
   assert stack;name=stack.pop();closing=line.split()[1:];assert not closing or closing[0]==name
 assert not stack

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--freeze-inputs',type=Path,required=True);args=ap.parse_args()
 lock=load(args.freeze_inputs);assert lock['status']=='OWNER_FROZEN_SOURCE_BP_INPUTS'and lock['owner_freeze_signal'].strip()
 for p,h in lock['sha256'].items():assert sha(Path(p).read_bytes())==h,('Frozen input drift',p)
 result=O/'final-installed-static-review.json';assert not result.exists(),'One-time review already frozen'
 C=load(O.parent/'final363/offline-review-inputs.json');assert C['fixed_base_revision']==BASE and C['fixed_additive_revision']==ADD
 initial=load(A/'initial-port-plan.json');fp=load(Path(C['base323_fingerprint_path']));assert sha(Path(C['base323_fingerprint_path']).read_bytes())==C['base323_fingerprint_sha256']
 P=A/'additive40-frozen-preparation';M=load(P/'module-provenance-plan.json');B=load(P/'blueprint-provenance-plan.json');S=load(A/'additive40-original-prerequisite-extracts/plan.json');closed=load(A/'additive40-prerequisite-integration-preparation/plan-with-owner-import-closure.json')
 assert S==closed and len(M)==len(B)==40 and len(S)==10
 provenance=load(A/'provenance.json');bp_records=load(A/'blueprint-provenance.json');by_source={r['destination_path']:r for r in provenance};by_BP={r['destination_path']:r for r in bp_records};assert len(by_source)==len(provenance)and len(by_BP)==len(bp_records)
 base_paths={r['destination_path']for r in C['base323_source_identities']};assert len(base_paths)==323
 added_paths={r['destination_path']for r in M+S};assert len(added_paths)==len(M)+len(S)and base_paths.isdisjoint(added_paths);assert set(by_source)==base_paths|added_paths
 BP_paths=set(C['base309_BP_paths'])|{r['destination_path']for r in B};assert len(BP_paths)==len(C['base309_BP_paths'])+len(B)and set(by_BP)==BP_paths
 # Guard every input and every public mathematical source; output files are separate.
 observed=[*R.joinpath('Hironaka').rglob('*.lean'),*R.joinpath('blueprint').glob('*.tex'),R/'Hironaka.lean']+[Path(p)for p in lock['sha256']]
 before=fingerprint(observed)
 for p,h in initial['existing_destination_math_source_digests'].items():assert sha((R/p).read_bytes())==h,p
 for p,h in initial['existing_blueprint_tex_digests'].items():
  if p!='blueprint/extensions.tex':assert sha((R/p).read_bytes())==h,p
 for p,h in initial['toolchain_profiles'].items():assert sha((R/p).read_bytes())==h,p
 for p in base_paths:assert sha((R/p).read_bytes())==fp[p],p
 base_parts=load(A/'base323-frozen-before-additive40/immutable-base-source-and-kernel-parts.json')['records'];assert len(base_parts)==len(base_paths)
 for row in base_parts:
  assert sha((R/row['source']).read_bytes())==row['source_sha256']
  for part in row['kernel_parts']:assert sha((R/part['path']).read_bytes())==part['sha256'],part['path']
 sys.path.insert(0,str(R/'scripts'));sys.path.insert(0,str(A));import upstream_namespace_map as names
 names.set_api_modules(['TranscendentalNakamaye.Pending.HironakaAPI'+s for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
 frozen=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'),env);relocate=env['relocate']
 tree=ast.parse((P/'frozen-inputs/sync_frozen_sources.py').read_text());HEADER=ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='HEADER'for t in n.targets)))
 contexts=load(A/'additive40-original-elaboration-contexts.json');adjust=contexts['contexts'];extra_imports=load(A/'additive40-original-support-imports.json')['imports'];notation={r['destination_module']for r in load(P/'seven-notation-source-generation-initial.json')['parents']}
 selective=[];ancestors=[]
 for m,ops in adjust.items():
  assert m in {r['destination_module']for r in M}
  for op in ops:
   if op['before'].startswith('open '):
    assert op['after']==op['before'].replace('open ','open _root_.Hironaka.',1);selective.append((m,op))
   else:
    command,rest=op['after'].split('\n',1);assert rest==op['before']and re.fullmatch(r'attribute \[local instance 2000\] (?:SubsemiringClass.toAddSubmonoidClass|IsOrderedRing.toIsOrderedAddMonoid) in',command);ancestors.append((m,op))
 assert len(selective)==9 and len({m for m,_ in selective})==8 and len(ancestors)==11 and len({m for m,_ in ancestors})==6
 assert not notation.intersection({m for m,_ in selective})
 assert len(contexts['authentic_class_ancestor_restorations'])==len(ancestors)
 for item in contexts['authentic_class_ancestor_restorations']:
  assert item['existing_original_instance_ancestor']in item['command']and item['original_declaration_payload_edits']==0
  assert any(m==item['destination_module']and op['after'].startswith(item['command']+'\n')and item['anchor']in op['before']for m,op in ancestors)
 source_checks=[]
 for row in M:
  raw=original(ADD,row['source_path']);assert sha(raw)==row['source_sha256']and(P/'original'/row['source_path']).read_bytes()==raw
  expected=HEADER+relocate(raw.decode());assert sha(expected)==row['destination_sha256']and(P/row['candidate_path']).read_text()==expected
  extras=extra_imports.get(row['destination_module'],[])
  if extras:
   at=re.search(r'^import ',expected,re.M).start();expected=expected[:at]+''.join('import '+m+'\n'for m in extras)+expected[at:]
  for op in adjust.get(row['destination_module'],[]):assert expected.count(op['before'])==1;expected=expected.replace(op['before'],op['after'],1)
  assert (R/row['destination_path']).read_text()==expected and by_source[row['destination_path']]['destination_sha256']==sha(expected)
  source_checks.append({'path':row['destination_path'],'original_sha256':sha(raw),'installed_sha256':sha(expected),'whole_original_preserved':True,'administrative_contexts':adjust.get(row['destination_module'],[]),'pure_imports':extras})
 # Every helper is a complete original declaration in the fixed source, not a synthetic replacement.
 support_checks=[];selected=[]
 for row in S:
  raw=original(ADD,row['source_path']);assert raw==original(BASE,row['source_path'])and sha(raw)==row['source_sha256']
  chunks=row['original_payload_chunks'];assert '\n'.join(chunks)==row['original_selected_source']and sha(row['original_selected_source'])==row['original_selected_sha256'];assert all(raw.decode().count(c)==1 for c in chunks)
  expected='';used=[]
  for part in row['canonical_source_layout']:
   if 'original_payload_index'in part:used.append(part['original_payload_index']);expected+=relocate(chunks[part['original_payload_index']])
   else:
    c=part['canonical_administrative_context'];assert sha(c)==part['sha256'];assert not re.search(r'^\s*(?:(?:private|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|example)\s',strip_comments(c),re.M);expected+=c
  assert sorted(used)==list(range(len(chunks)))and len(used)==len(chunks)
  scope_balance(expected);assert sha(expected)==row['prepared_destination_sha256']and (R/row['destination_path']).read_text()==expected
  draft=A/row['original_draft_path'];assert sha(draft.read_bytes())==row['original_draft_sha256']
  no_imports=lambda s:re.sub(r'^import [^\n]+\n','',s,flags=re.M)
  assert no_imports(expected)==no_imports(draft.read_text()),('Support non-import delta',row['destination_module'])
  selected.extend(row['complete_original_declarations']);support_checks.append({'path':row['destination_path'],'original_sha256':sha(raw),'selected_payload_sha256':row['original_selected_sha256'],'installed_sha256':sha(expected),'complete_original_declarations':row['complete_original_declarations'],'original_draft_sha256':row['original_draft_sha256'],'only_additional_owner_imports_since_peer':True})
 assert len(selected)==len(set(selected))==40
 # Independent complete chapter/node and original written-proof comparison.
 nodeplan=load(A/'blueprint-original-node-extract-plan.json');assert nodeplan['native_revision']==BASE;extracts=nodeplan['extracts'];assert len(extracts)==3
 BP_checks=[];new_node_checks=[]
 for path,row in by_BP.items():
  rev=row['published_source_revision'];assert rev in [BASE,ADD];raw=original(rev,row['source_path']);assert sha(raw)==row['source_sha256'];actual=(R/path).read_text();assert sha(actual)==row['destination_sha256'];assert actual.count('\\begin{proof}')==actual.count('\\end{proof}')==row['proofs'];assert actual.count('\\begin{definition}')==row['definitions']
  if path in extracts:
   spec=extracts[path];assert sha(raw)==spec['source_sha256'];labels=[l for l in re.findall(r'\\label\{([^}]+)\}',actual)if not l.startswith('sec:')];assert labels==spec['labels']
   for n in spec['complete_original_node_ranges']:
    for label in n['labels']:
     original_node=block(raw.decode(),label);current_node=block(actual,label);assert strip_attachments(names.rename_text_names(original_node))==strip_attachments(current_node),(path,label)
     before_bindings=bindings(original_node,'lean');assert before_bindings==n['original_bindings'];current_bindings=bindings(current_node,'lean')+[names.rename_text_names(v)for v in bindings(current_node,'upstreamlean')];assert sorted(names.rename_text_names(v)for v in before_bindings)==sorted(current_bindings),(path,label,'Original binding lost')
     new_node_checks.append({'path':path,'label':label,'original_core_sha256':sha(original_node),'installed_core_sha256':sha(current_node),'whole_statement_proof_math_preserved':True})
   for item in spec.get('additional_original_node_layout',[]):
    core=block(raw.decode(),item['label']);following=item['following_original_text'];assert sha(following)==item['following_original_text_sha256'];assert raw.decode().startswith(core+following,raw.decode().index(core));expected_tail=names.rename_text_names(following);present=block(actual,item['label']);assert actual.startswith(present+expected_tail,actual.index(present)),item['label']
    if item.get('context_before'):
     c=item['context_before'];lo,hi=item['original_context_lines'];assert ''.join(raw.decode().splitlines(True)[lo-1:hi])==c and sha(c)==item['context_before_sha256'];assert names.rename_text_names(c)in actual
   if path=='blueprint/maximal-contact.tex':
    tail='The two monotonicity statements are immediate from the definitions';assert actual.count(tail)==1;assert '\\label{mc:derivative-marked}'in actual
  elif path in C['base309_BP_paths']:assert sha(actual)==fp[path],('Unapproved base whole-chapter delta',path)
  else:
   candidate=next(r for r in B if r['destination_path']==path);assert actual==(P/candidate['candidate_path']).read_text()and sha(actual)==candidate['destination_sha256']
   orig_proofs=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',raw.decode(),re.S);now_proofs=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',actual,re.S);assert len(orig_proofs)==len(now_proofs)==candidate['proofs'];assert all(names.rename_text_names(x)==y for x,y in zip(orig_proofs,now_proofs))
  BP_checks.append({'path':path,'source_sha256':sha(raw),'installed_sha256':sha(actual),'proofs':row['proofs'],'definitions':row['definitions']})
 upstream={v for path in BP_paths for v in bindings((R/path).read_text(),'upstreamlean')};expected_upstream={v for spec in extracts.values()for v in spec['separately_verified_original_bindings'].values()};assert upstream==expected_upstream and len(upstream)==17
 # Read-only native witnesses are evidence, never replayed by this checker.
 native14=load(A/'actual-original-controlled-transform-subset-binding.json');assert native14 and 'controlledTransform_of_subset_cosupport'in json.dumps(native14)
 new3=load(A/'support-prep/principal-additive-blueprint-coverage/generator-update/three-upstream-only-bindings-evidence.json');assert len(new3['bindings'])==3
 # Whole-module deferral remains exact and outside every retained dependency.
 partition=load(A/'deferred-complete-module-partition.json');deferred={r['module']for r in partition['deferred_complete_modules']};assert deferred=={'Hironaka.Resolution.HironakaOriginalGlobalOffZero','Hironaka.Resolution.HironakaOriginalGlobalProperModification'};deferred_labels=set()
 for row in partition['deferred_complete_modules']+partition['deferred_complete_blueprint_chapters']:
  assert not(R/row['destination_path']).exists();raw=(A/row['canonical_draft_capture']).read_bytes();assert sha(raw)==row['sha256']
  if row['destination_path'].endswith('.tex'):deferred_labels.update(re.findall(r'\\label\{([^}]+)\}',raw.decode()))
 assert len(deferred_labels)==7
 for path in BP_paths:
  refs={v.strip()for g in re.findall(r'\\(?:uses|ref|eqref)\{([^}]+)\}',(R/path).read_text())for v in g.split(',')};assert not refs.intersection(deferred_labels),path
 physical={str(p.relative_to(R))for p in(R/'Hironaka').rglob('*.lean')}|{'Hironaka.lean'};assert physical==set(initial['existing_destination_math_source_digests'])|set(by_source)|{'Hironaka.lean'}
 imported={p.removesuffix('.lean').replace('/','.'):re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',(R/p).read_text(),re.M)for p in physical};assert not any(deferred.intersection(v)for v in imported.values());seen=set()
 def visit(m):
  if m in seen:return
  assert m in imported,m;seen.add(m)
  for dep in imported[m]:
   if dep=='Hironaka'or dep.startswith('Hironaka.'):visit(dep)
 visit('Hironaka');assert seen==set(imported)
 prepared_roots=(P/'candidate-root-imports.txt').read_text();prepared_master=(P/'candidate-blueprint-inputs.txt').read_text()
 roots=''.join('import '+r['destination_module']+'\n'for r in M)
 masterblock=''.join('\\input{'+Path(r['destination_path']).stem+'}\n'for r in B)
 assert set(roots.splitlines())==set(prepared_roots.splitlines())and len(roots.splitlines())==len(prepared_roots.splitlines())==len(M)
 assert set(masterblock.splitlines())==set(prepared_master.splitlines())and len(masterblock.splitlines())==len(prepared_master.splitlines())==len(B)
 def exact_added_block(text,addition,baseline):
  return next(c for c in [addition,addition+'\n','\n'+addition]if text.count(c)==1 and text.replace(c,'',1)==baseline)
 root=(R/'Hironaka.lean').read_text();master=(R/'blueprint/extensions.tex').read_text();rootblock=exact_added_block(root,roots,(O.parent/'final363/base323-Hironaka.lean').read_text());masterdelta=exact_added_block(master,masterblock,(O.parent/'final363/base323-extensions.tex').read_text());assert len(re.findall(r'\\input\{',master))==969
 # No-op replay is strictly read-only: intercept the historical unconditional receipt write.
 saved_text=Path.write_text;saved_bytes=Path.write_bytes;saved_unlink=Path.unlink;captured=[]
 def guarded_text(p,text,*a,**kw):
  assert p.resolve()==(A/'source-replay-receipt.json').resolve(),('Unexpected replay write',str(p));assert p.read_bytes()==text.encode();captured.append({'path':str(p),'sha256':sha(text)});return len(text)
 def deny(*a,**kw):raise AssertionError('Source-only check attempted a filesystem mutation')
 log=io.StringIO();argv=sys.argv[:]
 try:
  Path.write_text=guarded_text;Path.write_bytes=deny;Path.unlink=deny
  sys.argv=[str(A/'sync_frozen_sources.py'),'--source-root','/workspace/archon-publish','--revision',BASE,'--check','--additive40']
  with contextlib.redirect_stdout(log):runpy.run_path(str(A/'sync_frozen_sources.py'),run_name='__main__')
 finally:Path.write_text=saved_text;Path.write_bytes=saved_bytes;Path.unlink=saved_unlink;sys.argv=argv
 assert len(captured)==1 and fingerprint(observed)==before,'A public source or frozen input changed during static review'
 counts={'old_Lean_sources_preserved':len(initial['existing_destination_math_source_digests']),'old_BP_files_preserved':len(initial['existing_blueprint_tex_digests']),'frozen_profiles_preserved':len(initial['toolchain_profiles']),'unchanged_base_source_records':len(base_paths),'whole_additive_modules':len(M),'complete_new_helper_modules':len(S),'complete_original_helper_declarations':len(selected),'total_new_source_records':len(provenance),'whole_source_facing_BP_chapters':len(bp_records),'complete_written_proofs':sum(r['proofs']for r in BP_checks),'definition_nodes':sum(r['definitions']for r in BP_checks),'newly_extended_selected_BP_nodes':len(new_node_checks),'master_inputs':len(re.findall(r'\\input\{',master)),'physical_and_reachable_Lean_modules_including_root':len(physical),'upstream_only_original_bindings':len(upstream),'selective_open_qualifications':len(selective),'declaration_local_old_instance_ancestors':len(ancestors),'deferred_whole_modules':len(deferred),'deferred_whole_BP_chapters':len(partition['deferred_complete_blueprint_chapters'])}
 output={'status':'PASS_FINAL_EXTENDED_INSTALLED_STATIC_SOURCE_BP_PRESERVATION_AND_NO_OP','owner_freeze_signal':lock['owner_freeze_signal'],'freeze_inputs_sha256':sha(args.freeze_inputs.read_bytes()),'source_revisions':[BASE,ADD],'counts':counts,'source_checks':source_checks,'support_checks':support_checks,'BP_checks':BP_checks,'original_complete_selected_node_checks':new_node_checks,'upstream_original_names':sorted(upstream),'exact_added_root_block':rootblock,'exact_added_master_block':masterdelta,'before_after_public_input_fingerprint_equal':True,'no_op_intercepted_equal_receipt':captured,'Lean_kernel_Expr_native_runtime_invocations':0,'production_mutations':0,'logical_type_or_proof_payload_edits':0,'runtime_completion_claimed':False}
 (O/'final-read-only-input-fingerprints.json').write_text(json.dumps(before,indent=2)+'\n');(O/'source-only-no-op.log').write_text(log.getvalue());result.write_text(json.dumps(output,ensure_ascii=False,indent=2)+'\n');print(result);print(sha(result.read_bytes()))
if __name__=='__main__':main()
