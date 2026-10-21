"""Draft-only exact original payload/context extraction; no production/runtime."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parents[2];R=A.parents[1];REV='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'),env);relocate=env['relocate']
closure=Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication/native8-recursive-callee-closure/ordinary-source-declarations-by-parent.json');groups=json.loads(closure.read_text())
specs=[{'folder':'setup-additive-normal-derivative','short':'NormalDerivativeChart','draft':'NormalDerivativeChartIdealOriginalExact.lean','old':'Hironaka.MarkedIdeal.NormalDerivativeChart','chosen':['nd_nil','nd_mem_iterDerivIdeal'],'native_prefix':'TranscendentalNakamaye.Pending.NormalDerivativeChart.FlatChart.','before':[(4,5),(26,27),(29,29),(31,32),(34,34),(36,36),(56,56),(58,58)],'after':[(215,215),(217,217),(219,219)],'BP':'maximal-contact','labels':['mc:flat-chart','mc:normal-derivative-ideal']},{'folder':'setup-additive-order-powers','short':'OrderMultiplicativity','draft':'OrderMultiplicativityCosupportOriginalExact.lean','old':'Hironaka.Invariant.OrderMultiplicativity','chosen':['cosupport_idealPow_mul_eq'],'native_prefix':'TranscendentalNakamaye.Pending.OrderMultiplicativity.','before':[(4,5),(35,36),(38,38),(40,44),(46,46),(122,122),(124,124),(150,150),(269,269)],'after':[(291,291),(293,293),(295,295)],'BP':'hironaka','labels':['hir:marked-ideal-operations','hir:order-power']}]
for S in specs:
 O=A/'support-prep'/S['folder'];original=O/(S['short']+'.original.lean.txt');raw=original.read_bytes();text=raw.decode();lines=text.splitlines(keepends=True);src='TranscendentalNakamaye/TranscendentalNakamaye/Pending/'+S['short']+'.lean';assert subprocess.check_output(['git','-C','/workspace/archon-publish','show',REV+':'+src])==raw
 selected=[]
 for name in S['chosen']:
  m=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M);assert m,name
  start=text.rfind('/--',0,m.start());assert text.index('-/',start)<m.start()
  end=m.end()+re.search(r'\n\n(?=(?:/--|(?:end|section)\b))',text[m.end():]).start()+1;body=text[start:end];assert text.count(body)==1
  selected.append({'native_name':S['native_prefix']+name,'short_name':name,'start_byte':len(text[:start].encode()),'end_byte':len(text[:end].encode()),'start_line':text.count('\n',0,start)+1,'end_line':text.count('\n',0,end),'complete_original_payload':body,'sha256':sha(body.encode())})
 expected=next(g['complete_ordinary_original_declarations']for g in groups if g['actual_native_parent']=='TranscendentalNakamaye.Pending.'+S['short']);expected=[r['actual_original_declaration']if isinstance(r,dict)else r for r in expected];assert set(expected)=={r['native_name']for r in selected}
 contexts=[]
 def context(a,b):
  value=''.join(lines[a-1:b]);return {'start_line':a,'end_line':b,'original_source':value,'sha256':sha(value.encode())}
 before=[context(a,b)for a,b in S['before']];after=[context(a,b)for a,b in S['after']]
 layout=[{'canonical_administrative_context':'/- Complete original prerequisite; statement and mathematical proof unchanged. -/\nimport '+S['old']+'\n\n'}]
 for c in before:
  v=relocate(c['original_source'])+'\n';layout.append({'canonical_administrative_context':v,'original_context':c})
 for i,r in enumerate(selected):layout.extend([{'original_payload_index':i},{'canonical_administrative_context':'\n'}])
 for c in after:layout.append({'canonical_administrative_context':relocate(c['original_source'])+'\n','original_context':c})
 for p in layout:
  if'canonical_administrative_context'in p:p['sha256']=sha(p['canonical_administrative_context'].encode())
 chunks=[r['complete_original_payload']for r in selected];out=''.join(relocate(chunks[p['original_payload_index']])if'original_payload_index'in p else p['canonical_administrative_context']for p in layout)
 stack=[];trace=[]
 for n,line in enumerate(out.splitlines(),1):
  if line.startswith('namespace '):name=line[10:].strip();stack.append(name);trace.append([n,'namespace',name])
  elif re.match(r'^(?:noncomputable )?section(?: |$)',line):name=line.split('section',1)[1].strip();stack.append(name);trace.append([n,'section',name])
  elif re.match(r'^end(?: |$)',line):
   name=line[3:].strip();assert stack;opened=stack.pop();assert not name or name==opened,(name,opened);trace.append([n,'end',opened])
 assert not stack
 f=O/S['draft'];assert not f.exists();f.write_text(out)
 bpfile=O/(S['BP']+'.original.tex.txt');bpraw=bpfile.read_bytes();bp=bpraw.decode();bppath='TranscendentalNakamaye/blueprint/src/'+S['BP']+'.tex';assert subprocess.check_output(['git','-C','/workspace/archon-publish','show',REV+':'+bppath])==bpraw
 nodes=[]
 for label in S['labels']:
  i=bp.index('\\label{'+label+'}');openings=list(re.finditer(r'\\begin\{(definition|lemma|theorem|proposition|corollary)\}',bp[:i]));start=openings[-1].start();kind=openings[-1].group(1);envend=bp.index('\\end{'+kind+'}',i)+len('\\end{'+kind+'}')
  if kind=='definition':end=envend
  else:end=bp.index('\\end{proof}',envend)+len('\\end{proof}')
  node=bp[start:end]+'\n';p=O/(label.replace(':','--')+'.complete-original-node.tex.txt');assert not p.exists();p.write_text(node)
  binding=[v.strip()for g in re.findall(r'\\lean\{([^}]+)\}',node)for v in g.split(',')]
  nodes.append({'label':label,'environment':kind,'capture':p.name,'start_line':bp.count('\n',0,start)+1,'end_line':bp.count('\n',0,end)+1,'start_byte':len(bp[:start].encode()),'end_byte_exclusive_before_added_terminal_newline':len(bp[:end].encode()),'sha256':sha(node.encode()),'complete_written_proofs':node.count('\\begin{proof}'),'complete_definition_nodes':int(kind=='definition'),'all_original_bindings':binding,'all_original_uses':[v.strip()for g in re.findall(r'\\uses\{([^}]+)\}',node)for v in g.split(',')],'statement_and_proof_changes':0,'capture_only_not_installed':True})
 assert {r['native_name']for r in selected}<={v for n in nodes for v in n['all_original_bindings']}
 old=R/(S['old'].replace('.','/')+'.lean');assert old.is_file()
 d={'status':'DRAFT_ONLY_COMPLETE_ORIGINAL_SELECTED_SUPPORT_ACTUAL_ORDINARY_CLOSURE_MATCH','fixed_ordinary_revision':REV,'source_path':src,'source_git_blob':subprocess.check_output(['git','-C','/workspace/archon-publish','rev-parse',REV+':'+src],text=True).strip(),'whole_original_source_sha256':sha(raw),'destination_module':'Hironaka.Support.'+Path(S['draft']).stem,'draft_path':f.name,'draft_sha256':sha(out.encode()),'draft_lines':len(out.splitlines()),'complete_original_declarations':[r['native_name']for r in selected],'selected_payloads':selected,'original_payload_chunks':chunks,'original_selected_source':'\n'.join(chunks),'original_selected_sha256':sha('\n'.join(chunks).encode()),'canonical_source_layout':layout,'complete_original_active_contexts_before_payloads':before,'complete_original_active_closings':after,'original_universe_context':'Original Type* binders retained literally; no explicit universe declarations inserted or rewritten.','no_active_include_omit_or_local_instance_commands_in_selected_context':True,'scope_trace':trace,'all_named_and_anonymous_closings_balanced':True,'frozen_original_owner_import':{'module':S['old'],'path':str(old.relative_to(R)),'sha256':sha(old.read_bytes()),'unchanged':True},'actual_ordinary_closure':{'path':str(closure),'sha256':sha(closure.read_bytes()),'exact_same_parent_set_confirmed':True,'runtime_not_repeated':True},'blueprint':{'source_path':bppath,'whole_original_source_sha256':sha(bpraw),'git_blob':subprocess.check_output(['git','-C','/workspace/archon-publish','rev-parse',REV+':'+bppath],text=True).strip(),'complete_original_nodes':nodes,'original_bindings_retained_for_later_actual_local_upstream_classification':True},'mathematical_statement_or_proof_payload_edits':0,'production_source_BP_Git_edits':False,'Lean_build_kernel_Expr_invocations':0,'publication_compile_or_expression_PASS_claimed':False,'notes':(['mc:flat-chart is the complete original definition node; nd_nil is the direct inverse-coordinate identity covered there. mc:normal-derivative-ideal supplies the complete original written proof for the substantive ideal-derivative assertion.']if S['short']=='NormalDerivativeChart'else['hir:marked-ideal-operations directly binds the selected cosupport identity and supplies its full proof. hir:order-power is also captured as the complete original supporting prerequisite proof; its installation is not silently required or claimed.'])}
 p=O/'extraction-audit.json';assert not p.exists();p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(f,sha(f.read_bytes()),len(out.splitlines()));print(p,sha(p.read_bytes()));print('BP',[(n['label'],n['complete_written_proofs'],len(n['all_original_bindings']))for n in nodes])
