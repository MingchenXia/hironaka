from pathlib import Path
import json,hashlib
W=Path('/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/support-prep/principal-additive-blueprint-coverage')
p=json.loads((W/'complete-original-node-integration-plan.json').read_text());source=W/'maximal-contact.tex.whole-original.txt';raw=source.read_bytes();lines=raw.decode().splitlines(keepends=True);sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
def L(a,b):return ''.join(lines[a-1:b])
# Original subsection headers and ALL original shared assumption/notation paragraphs.
specs=[('derivative-blowup-scope',189,196,'mc:derivative-marked',['mc:derivative-marked','mc:inclusions-tower'],'Blowup map, exceptional divisor, controlled transform, ambient N=M, charts and directional-derivative notation.'),('coefficient-sum-scope',1060,1063,'mc:finite-sum',['mc:finite-sum','mc:marked-finite-sum','mc:marked-finite-sum-tower','mc:coefficient-ideal','mc:coefficient-equivalent'],'All marked ideals have N=M; finite germ sums have their original stalkwise meaning.'),('coefficient-restriction-scope',1159,1163,'mc:restrict-marked',['mc:restrict-marked','mc:restrict-tower','mc:coefficient-restriction-support','mc:coefficient-restriction-tower'],'SAME B=(M,M,E,b,d) with b coherent; SAME I=(M,M,E,a,mu), a coherent and mu>=1; original sources.'),('normal-coefficient-full-scope',1291,1295,'mc:flat-chart',['mc:flat-chart','mc:normal-derivative-ideal','mc:normal-coefficient-invariant','mc:normal-coefficient-step','mc:coefficient-restriction-full'],'Original normal-coefficient tracking subsection description and actual normal-derivative notation.')]
records=[]
for name,lo,hi,before,applies,note in specs:
 s=L(lo,hi);f=name+'.complete-original-context.tex.txt';(W/f).write_text(s)
 records.append({'source_parent':p['complete_original_source_parents']['maximal-contact.tex'],'original_lines':[lo,hi],'capture':f,'sha256':sha(s),'insert_before_label':before,'applies_to_labels':applies,'reason':note,'original_text':s,'context_text_edits':0})
tail=L(410,411);assert tail.startswith('The two monotonicity statements') and tail.endswith('\\).\n')
tailfile='mc--derivative-marked.original-following-justification-lines410-411.tex.txt';(W/tailfile).write_text(tail)
tailrow={'label':'mc:derivative-marked','source_parent':p['complete_original_source_parents']['maximal-contact.tex'],'original_core_range':[399,409],'original_tail_range':[410,411],'required_complete_range_including_tail':[399,411],'tail_capture':tailfile,'tail_sha256':sha(tail),'native_tail_text':tail,'generator_instruction':'Use explicit original end-line/range override through line411 (or append exactly lines410–411) AFTER the native definition environment. The generic block() ending at end{definition} omits this original proof prose. Preserve it exactly once, not as an invented proof environment.','proof_text_edits':0}
rows={r['label']:r for r in p['node_records']};seq=[]
for label in p['proposed_new_excerpt_chapter_groups']['NEW maximal-contact support excerpt']:
 for c in records:
  if c['insert_before_label']==label:seq.append(c['original_text'])
 text=(W/rows[label]['full_node_with_native_trailing_prose_capture']).read_text();seq.append(text)
result='\n\n'.join(s.rstrip('\n') for s in seq)+'\n'
f='proposed-maximal-contact-complete-original-node-sequence-WITH-CONTEXT.tex.txt';(W/f).write_text(result)
assert result.count(tail.rstrip('\n'))==1
assert result.count('\\begin{proof}')==12
assert result.count('\\begin{definition}')==5
assert sum(result.count('\\label{'+l+'}') for l in p['proposed_new_excerpt_chapter_groups']['NEW maximal-contact support excerpt'])==16
for c in records:assert result.count(c['original_text'].rstrip('\n'))==1
for label in p['proposed_new_excerpt_chapter_groups']['NEW maximal-contact support excerpt']:
 core=(W/rows[label]['core_capture']).read_text();assert core.rstrip('\n') in result
plan={'status':'READ_ONLY_AUTHENTIC_CONTEXT_AND_EXACT_TAIL_OVERRIDE_PLAN','source_revision':p['revision'],'source_parent':p['complete_original_source_parents']['maximal-contact.tex'],'original_context_before_label_segments':records,'explicit_original_tail_overrides':[tailrow],'maximal_contact_exact_sixteen_node_audit_sequence_with_context':{'file':f,'sha256':sha(result),'nodes':16,'written_proofs':12,'definitions':5,'all_original_node_statement_proof_payloads_retained':True,'all_four_authentic_context_blocks_exact_once':True,'explicit_two_line_definition_justification_exact_once':True},'hironaka_node_context_assessment':[{'label':l,'assessment':'Original complete node explicitly supplies its hypotheses and notation (ideals/marks/N, blowup/centre, or well-formed marked ideal/Eprime/S). No standing antecedent or subsection hypothesis is omitted. Native following proof/clarification remains in full-node capture.','extra_context_required':False} for l in p['proposed_new_excerpt_chapter_groups']['NEW hironaka support excerpt']],'scope_preservation_notes':['The already-retained first-six maximal-contact contexts stay immutable; this is a separate NEW excerpt plan.','Do not infer hypotheses from a distant missing subsection. Insert each exact source context immediately before its first selected label.','Do not import the full maximal-contact chapter or rewrite statements/proofs to make them self-contained.','The optional normal Taylor nodes belong within the original normal-coefficient subsection if root later selects them, before mc:flat-chart.','No production generator, master, source, status, Lean runtime, kernel or expression gate was edited or run.'],'production_or_runtime_changes':False}
(W/'authentic-context-and-tail-integration-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'plan_sha256':sha((W/'authentic-context-and-tail-integration-plan.json').read_bytes()),'sequence_sha256':sha(result),'context_ranges':[r['original_lines'] for r in records],'tail_range':[410,411]},indent=2))
