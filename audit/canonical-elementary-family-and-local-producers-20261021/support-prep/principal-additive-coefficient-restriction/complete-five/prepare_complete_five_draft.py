from pathlib import Path
import ast, hashlib, json, re, subprocess, sys
R=Path('/workspace/hironaka'); A=R/'audit/canonical-elementary-family-and-local-producers-20261021'
H=A/'support-prep/principal-additive-coefficient-restriction'; W=H/'complete-five'
U=Path('/workspace/archon-publish'); rev='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
sha=lambda x:hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
history={p.name:sha(p.read_bytes()) for p in H.iterdir() if p.is_file()}
(W/'immutable-three-declaration-history-fingerprints.json').write_text(json.dumps(history,indent=2)+'\n')
source_path='TranscendentalNakamaye/TranscendentalNakamaye/Pending/CoefficientIdealRestriction.lean'
bp_path='TranscendentalNakamaye/blueprint/src/maximal-contact.tex'
def gitshow(path):return subprocess.check_output(['git','-C',str(U),'show',rev+':'+path])
def blob(path):return subprocess.check_output(['git','-C',str(U),'rev-parse',rev+':'+path]).decode().strip()
raw=gitshow(source_path); text=raw.decode(); lines=text.splitlines(keepends=True)
assert raw==(H/'CoefficientIdealRestriction-whole-original.lean.txt').read_bytes()
(W/'CoefficientIdealRestriction-whole-original.lean.txt').write_bytes(raw)
bpraw=gitshow(bp_path); bp=bpraw.decode(); (W/'maximal-contact-whole-original-fixed-native.tex.txt').write_bytes(bpraw)
def L(a,b):return ''.join(lines[a-1:b])
verifier=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
sys.path.insert(0,str(R/'scripts')); import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']]); flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
node=next(n for n in ast.parse(verifier.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[node],type_ignores=[]),str(verifier),'exec'),env);relocate=env['relocate']
selected=[('cosupport_coeff_subset',130,161,'OneSpace'),('centresIn_of_isGeoTestTower_withN',187,195,'Tower'),('isCoherent_coeffMarked',241,243,'Tower'),('cosupp_coeff_withN',245,253,'Tower'),('coeff_restrict_tower',255,273,'Tower')]
payloads=[]
for name,lo,hi,scope in selected:
 s=L(lo,hi);assert text.count(s)==1 and 'theorem '+name in s
 assert relocate(s)==s,'No proof/type token relocation is expected in these five payloads'
 (W/(name+'-complete-original-declaration.lean.txt')).write_text(s)
 payloads.append({'native_name':'TranscendentalNakamaye.Pending.CoefficientIdealRestriction.'+name,'public_name':'Hironaka.CoefficientIdealRestriction.'+name,'original_lines':[lo,hi],'scope':scope,'sha256':sha(s),'original_selected_source':s})
# Preserve all original active section-variable commands, even the unused Mprime binders.
common_ranges=[(5,6),(48,60)]
one_ranges=[(64,66),(95,96)]
tower_range=(167,169)
common='\n'.join(L(a,b) for a,b in common_ranges)+'\n'
one='\n'.join(L(a,b) for a,b in one_ranges)+'\n'
close_one=L(163,163);tower=L(*tower_range);closing=L(275,279)
assert close_one=='end OneSpace\n'
assert closing=='end Tower\n\nend\n\nend TranscendentalNakamaye.Pending.CoefficientIdealRestriction\n'
context={'common':common,'OneSpace':one,'close_OneSpace':close_one,'Tower':tower,'closing_all':closing}
for k,v in context.items():(W/('original-context-'+k+'.lean.txt')).write_text(v)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
imports=['Hironaka.MarkedIdeal.CoefficientIdealRestriction','Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact']
draft=header+''.join('import '+m+'\n' for m in imports)+'\n'+relocate(common)+relocate(one)+payloads[0]['original_selected_source']+'\n'+close_one+'\n'+relocate(tower)+'\n'+'\n'.join(p['original_selected_source'] for p in payloads[1:])+'\n'+relocate(closing)
out=W/'CoefficientRestrictionSupportOriginalExact.lean';out.write_text(draft)
for p in payloads:assert draft.count(p['original_selected_source'])==1
stack=[];scope_commands=[]
for i,l in enumerate(draft.splitlines(),1):
 if re.match(r'^namespace ',l):stack.append(('namespace',l.split(' ',1)[1]));scope_commands.append([i,l])
 elif l=='noncomputable section':stack.append(('section',None));scope_commands.append([i,l])
 elif re.match(r'^section ',l):stack.append(('section',l.split(' ',1)[1]));scope_commands.append([i,l])
 elif re.match(r'^end(?: |$)',l):
  label=l[3:].strip() or None; assert stack
  kind,name=stack.pop();assert label==name,(i,l,kind,name);scope_commands.append([i,l])
assert not stack and len(re.findall(r'^theorem ',draft,re.M))==5
assert not re.search(r'^\s*(include|omit|attribute.*instance|local instance|scoped instance)\b',text,re.M)
# Retain complete original blueprint nodes, including source/uses/lean/status and entire written proofs.
labels=['mc:restrict-marked','mc:restrict-tower','mc:coefficient-restriction-support','mc:coefficient-restriction-tower','mc:coefficient-ideal','mc:marked-finite-sum','mc:finite-sum','mc:coefficient-equivalent']
bprows=[];parts=[]
for label in labels:
 key='\\label{'+label+'}';assert bp.count(key)==1;pos=bp.index(key)
 beg=list(re.finditer(r'\\begin\{(definition|lemma|theorem|proposition)\}',bp[:pos]))[-1];kind=beg.group(1)
 end=bp.index('\\end{'+kind+'}',pos)+len('\\end{'+kind+'}')
 if re.match(r'\s*\\begin\{proof\}',bp[end:]):end=bp.index('\\end{proof}',end)+len('\\end{proof}')
 if end<len(bp) and bp[end]=='\n':end+=1
 s=bp[beg.start():end];assert bp.count(s)==1;filename=label.replace(':','-')+'-complete-original-node.tex.txt'
 (W/filename).write_text(s);parts.append(s)
 retained=[]
 for q in (R/'blueprint').rglob('*.tex'):
  qs=q.read_text()
  if key in qs:retained.append({'path':str(q.relative_to(R)),'sha256':sha(qs),'contains_exact_native_node':s in qs,'contains_namespace_relocated_node':names.rename_text_names(s) in qs})
 bprows.append({'label':label,'native_lines':[bp.count('\n',0,beg.start())+1,bp.count('\n',0,end)],'native_node_file':filename,'sha256':sha(s),'environment':kind,'written_proof_count':s.count('\\begin{proof}'),'native_lean_attachments':re.findall(r'\\lean\{([^}]*)\}',s),'retained_production_nodes':retained})
(W/'complete-native-blueprint-node-attachments.tex.txt').write_text('\n'.join(parts))
base=Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication/native40-callee-preflight/base-actual-name-observations.json');rows=json.loads(base.read_text());owners={}
for r in rows:owners.setdefault(r['actual_name'],[]).append(r['module'])
needed=['Hironaka.CoefficientIdealRestriction.N_geoTransformAlong_withN','Hironaka.CoefficientIdealRestriction.restrict_tower','Hironaka.CoefficientIdealRestriction.cosupp_inter_subset_cosupp_withN','Hironaka.CoefficientIdeal.isAmbientFamily_derivMarked','Hironaka.CoefficientIdeal.IsAmbientFamily.isCoherent_msum','Hironaka.CoefficientIdeal.coeffMarked','Hironaka.CoefficientIdeal.coeff_tower']
plan={'status':'DRAFT_ONLY_AUTHORIZED_EXACT_FIVE_COMPLETE_ORIGINAL_DECLARATIONS_NO_RUNTIME','source_module':'TranscendentalNakamaye.Pending.CoefficientIdealRestriction','source_path':source_path,'published_source_revision':rev,'source_git_blob':blob(source_path),'source_sha256':sha(raw),'source_line_count':len(lines),'whole_source_capture':'CoefficientIdealRestriction-whole-original.lean.txt','destination_module_suggestion':'Hironaka.Support.CoefficientRestrictionSupportOriginalExact','destination_path_suggestion':'Hironaka/Support/CoefficientRestrictionSupportOriginalExact.lean','draft_file':out.name,'draft_sha256':sha(draft),'immutable_superseded_three_declaration_draft':{'path':str(H/'CoefficientRestrictionSupportOriginalExact.lean'),'sha256':history['CoefficientRestrictionSupportOriginalExact.lean'],'history_fingerprints':'immutable-three-declaration-history-fingerprints.json','all_history_bytes_preserved':True},'complete_original_declarations':payloads,'original_context_blocks':[{'original_lines':[a,b],'text':L(a,b),'sha256':sha(L(a,b))} for a,b in common_ranges+one_ranges+[tower_range]],'original_closings':[{'original_lines':[163,163],'text':close_one,'sha256':sha(close_one)},{'original_lines':[275,279],'text':closing,'sha256':sha(closing)}],'all_balanced_scope_commands':scope_commands,'authentic_unused_context_retained':'Original Mprime and its manifold instances at lines95–96 remain verbatim inside OneSpace. They are closed before Tower, exactly as in the original. No include/omit/local-instance commands occur in the file.','existing_pure_imports':[{'module':m,'path':m.replace('.','/')+'.lean','sha256':sha((R/(m.replace('.','/')+'.lean')).read_bytes())} for m in imports],'prerequisite_actual_owner_observations':[{'name':n,'captured_actual_public_owners':owners.get(n,[])} for n in needed],'same_parent_recursive_prerequisites_closed':['cosupport_coeff_subset','coeff_restrict_tower'],'external_selected_support_needed':['TranscendentalNakamaye.Pending.CoefficientIdeal.coeff_tower'],'external_support_note':'The separate authorized CoefficientIdeal recursive closure is owned by root; its support module/import must be integrated before compile-readiness is claimed. This draft retains the genuine original coeff_tower call and changes no proof.','blueprint':{'fixed_revision':rev,'source_path':bp_path,'source_git_blob':blob(bp_path),'whole_source_sha256':sha(bpraw),'whole_capture':'maximal-contact-whole-original-fixed-native.tex.txt','complete_native_nodes':bprows,'direct_declaration_to_node':{'cosupport_coeff_subset':'mc:coefficient-restriction-support','centresIn_of_isGeoTestTower_withN':'mc:restrict-tower','isCoherent_coeffMarked':'mc:restrict-marked','cosupp_coeff_withN':'mc:coefficient-restriction-support','coeff_restrict_tower':'mc:coefficient-restriction-tower'},'coherence_written_proof_note':'The exact direct mc:restrict-marked definition node binds isCoherent_coeffMarked and states coherence but has no separate written proof. Its actual source proof is the derivative ambient-family plus marked-sum coherence; the entire original coefficient-ideal, marked-finite-sum and finite-sum nodes with both sum proofs are retained. No invented historical proof is asserted.','external_anchor_precision':'Direct requested labels currently have no retained production complete nodes. Audit carries exact entire original nodes/proofs for the production owner to attach; the existing mc:coefficient-ideal production node is only an external prerequisite and is not claimed byte-identical.'},'relocation_verifier':str(verifier.relative_to(R)),'relocation_verifier_sha256':sha(verifier.read_bytes()),'proof_type_payload_edits':0,'administrative_changes':['Pure imports of existing immutable old public modules','Standard release header','Frozen canonical namespace/open relocation','All original active OneSpace and Tower commands plus ALL balanced closings'],'runtime_build_kernel_or_Expr_export_performed':False,'production_edits_performed':False,'git_mutations_performed':False}
(W/'plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
check={'status':'PASS_SOURCE_ONLY_FIVE_COMPLETE_PAYLOADS_AND_BALANCED_AUTHENTIC_CONTEXTS','draft_sha256':sha(draft),'plan_sha256':sha((W/'plan.json').read_bytes()),'five_payloads_exact_once':True,'proof_type_payload_edits':0,'only_five_selected_theorem_commands':True,'whole_scope_stack_empty':True,'scope_commands':scope_commands,'superseded_three_draft_and_audit_unchanged':all(sha((H/n).read_bytes())==h for n,h in history.items()),'runtime_or_production_claim':False}
assert check['superseded_three_draft_and_audit_unchanged']
(W/'static-complete-payload-context-check.json').write_text(json.dumps(check,ensure_ascii=False,indent=2)+'\n')
(W/'REPORT.md').write_text('''# Five complete original coefficient-restriction declarations: draft only\n\nThe new draft contains exactly the authorized five complete fixed-4c6 declarations. Every original statement/proof byte is unchanged. The entire original source is retained; the initial three-declaration draft and audit remain immutable, with a separate before/after hash guard.\n\n`cosupport_coeff_subset` is placed in its authentic OneSpace section, including both original variable commands and the unused Mprime/manifold binders; the original OneSpace closing precedes the original Tower opening. The final Tower, anonymous noncomputable-section and namespace closings are all present.\n\nEight complete native blueprint nodes and six written proofs are captured. Direct attachments cover all five declarations. The coherence binding is honestly a definition node; its actual original coefficient/marked-sum/finite-sum supporting written proofs are retained separately. The fourth direct node, restricted coefficient ideals along towers, adds the exact complete native written proof for `coeff_restrict_tower`.\n\nThe same-parent ordinary closure is now included. Separate CoefficientIdeal support still must supply the genuine original `coeff_tower` and its selected prerequisites before compilation is claimed. No production source, root import, old artifact, Git state, Lean runtime, kernel or expression exporter was changed or run.\n''')
(W/'draft-fingerprints.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in W.iterdir() if p.is_file() and p.name!='draft-fingerprints.json'},indent=2)+'\n')
print(json.dumps({'draft':str(out),'draft_sha256':sha(draft),'plan_sha256':sha((W/'plan.json').read_bytes()),'payload_count':len(payloads),'bp_nodes':len(bprows),'written_proofs':sum(p['written_proof_count'] for p in bprows),'old_three_history_unchanged':True},indent=2))
