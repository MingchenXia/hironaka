from pathlib import Path
import ast, hashlib, json, re, subprocess, sys
R=Path('/workspace/hironaka')
A=R/'audit/canonical-elementary-family-and-local-producers-20261021'
W=A/'support-prep/principal-additive-coefficient-restriction'
U=Path('/workspace/archon-publish')
rev='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
source_path='TranscendentalNakamaye/TranscendentalNakamaye/Pending/CoefficientIdealRestriction.lean'
bp_path='TranscendentalNakamaye/blueprint/src/maximal-contact.tex'
sha=lambda x:hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def gitshow(path):return subprocess.check_output(['git','-C',str(U),'show',rev+':'+path])
def blob(path):return subprocess.check_output(['git','-C',str(U),'rev-parse',rev+':'+path]).decode().strip()
raw=gitshow(source_path); text=raw.decode(); lines=text.splitlines(keepends=True)
whole=W/'CoefficientIdealRestriction-whole-original.lean.txt'
assert whole.read_bytes()==raw
bpraw=gitshow(bp_path); bp=bpraw.decode()
(W/'maximal-contact-whole-original-fixed-native.tex.txt').write_bytes(bpraw)
# Load the already-frozen source relocation function without executing its verifier.
verifier=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
sys.path.insert(0,str(R/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
node=next(n for n in ast.parse(verifier.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
env={'re':re,'names':names,'flat':flat,'fq':fq}
exec(compile(ast.Module(body=[node],type_ignores=[]),str(verifier),'exec'),env)
relocate=env['relocate']
def L(lo,hi):return ''.join(lines[lo-1:hi])
# Preserve every active command for these declarations; OneSpace is already CLOSED.
context_ranges=[(5,6),(48,60),(167,169)]
assert L(167,169)=='section Tower\n\nvariable {n : ℕ} {X : CMfd.{u} n}\n'
context='\n'.join(L(a,b) for a,b in context_ranges)+'\n'
closing=L(275,279)
assert closing=='end Tower\n\nend\n\nend TranscendentalNakamaye.Pending.CoefficientIdealRestriction\n'
(W/'original-active-context.lean.txt').write_text(context)
(W/'original-balanced-closing.lean.txt').write_text(closing)
selected=[('centresIn_of_isGeoTestTower_withN',187,195),('isCoherent_coeffMarked',241,243),('cosupp_coeff_withN',245,253)]
payloads=[]
for name,lo,hi in selected:
 s=L(lo,hi);assert 'theorem '+name in s and text.count(s)==1
 (W/(name+'-complete-original-declaration.lean.txt')).write_text(s)
 payloads.append({'native_name':'TranscendentalNakamaye.Pending.CoefficientIdealRestriction.'+name,'public_name':'Hironaka.CoefficientIdealRestriction.'+name,'original_lines':[lo,hi],'sha256':sha(s),'original_selected_source':s})
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
imports=['Hironaka.MarkedIdeal.CoefficientIdealRestriction','Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact']
draft=header+''.join('import '+m+'\n' for m in imports)+'\n'+relocate(context)+'\n'.join(p['original_selected_source'] for p in payloads)+'\n'+relocate(closing)
# Here the three payloads contain no relocation-required identifiers; compare exact bytes.
for p in payloads:
 assert relocate(p['original_selected_source'])==p['original_selected_source']
 assert draft.count(p['original_selected_source'])==1
out=W/'CoefficientRestrictionSupportOriginalExact.lean'
out.write_text(draft)
# Actual currently captured public names, not text heuristics, establish imported prerequisites.
base=Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication/native40-callee-preflight/base-actual-name-observations.json')
rows=json.loads(base.read_text()); byname={}
for r in rows:byname.setdefault(r['actual_name'],[]).append(r['module'])
prereqs=['Hironaka.CoefficientIdealRestriction.N_geoTransformAlong_withN','Hironaka.CoefficientIdealRestriction.cosupp_inter_subset_cosupp_withN','Hironaka.CoefficientIdeal.isAmbientFamily_derivMarked','Hironaka.CoefficientIdeal.IsAmbientFamily.isCoherent_msum','Hironaka.CoefficientIdeal.coeffMarked','Hironaka.CoefficientIdealRestriction.cosupport_coeff_subset','Hironaka.CoefficientIdeal.coeff_tower']
# Capture COMPLETE native nodes, retaining all original lean attachments, uses and proof text.
labels=['mc:restrict-marked','mc:restrict-tower','mc:coefficient-restriction-support','mc:coefficient-ideal','mc:marked-finite-sum','mc:finite-sum']
bprows=[];nodeparts=[]
for label in labels:
 key='\\label{'+label+'}';assert bp.count(key)==1
 pos=bp.index(key)
 begins=list(re.finditer(r'\\begin\{(definition|lemma|theorem|proposition)\}',bp[:pos]))
 beg=begins[-1];kind=beg.group(1)
 end=bp.index('\\end{'+kind+'}',pos)+len('\\end{'+kind+'}')
 tail=bp[end:]
 nextproof=re.match(r'\s*\\begin\{proof\}',tail)
 if nextproof:end=bp.index('\\end{proof}',end)+len('\\end{proof}')
 if end<len(bp) and bp[end]=='\n':end+=1
 s=bp[beg.start():end]
 assert bp.count(s)==1
 filename=label.replace(':','-')+'-complete-original-node.tex.txt'
 (W/filename).write_text(s)
 # Check exact retained production node presence separately from mere external references.
 retained=[]
 for q in (R/'blueprint').rglob('*.tex'):
  qs=q.read_text()
  if key in qs:retained.append({'path':str(q.relative_to(R)),'sha256':sha(qs),'contains_exact_native_node':s in qs,'contains_namespace_relocated_node':names.rename_text_names(s) in qs})
 bprows.append({'label':label,'native_chapter':bp_path,'native_lines':[bp.count('\n',0,beg.start())+1,bp.count('\n',0,end)],'native_node_file':filename,'sha256':sha(s),'environment':kind,'written_proof_count':s.count('\\begin{proof}'),'native_lean_attachments':re.findall(r'\\lean\{([^}]*)\}',s),'retained_production_nodes':retained})
 nodeparts.append(s)
(W/'complete-native-blueprint-node-attachments.tex.txt').write_text('\n'.join(nodeparts))
plan={'status':'DRAFT_ONLY_COMPLETE_ORIGINAL_THREE_DECLARATIONS_NOT_RUNTIME_CHECKED','source_module':'TranscendentalNakamaye.Pending.CoefficientIdealRestriction','source_path':source_path,'published_source_revision':rev,'source_git_blob':blob(source_path),'source_sha256':sha(raw),'source_line_count':len(lines),'whole_source_capture':whole.name,'destination_module_suggestion':'Hironaka.Support.CoefficientRestrictionSupportOriginalExact','destination_path_suggestion':'Hironaka/Support/CoefficientRestrictionSupportOriginalExact.lean','draft_file':out.name,'draft_sha256':sha(draft),'complete_original_declarations':payloads,'original_context_blocks':[{'original_lines':[a,b],'text':L(a,b),'sha256':sha(L(a,b))} for a,b in context_ranges],'original_closing_lines':[275,279],'original_closing':closing,'original_closing_sha256':sha(closing),'balanced_closings':['end Tower','end (anonymous noncomputable section)','end TranscendentalNakamaye.Pending.CoefficientIdealRestriction'],'inactive_scope_note':'OneSpace lines64–163 is closed at line163; its M/Mprime variables and IsComplexManifold command do not apply inside Tower. No include/omit or local-instance commands occur in the original file.','existing_pure_imports':[{'module':m,'path':m.replace('.','/')+'.lean','sha256':sha((R/(m.replace('.','/')+'.lean')).read_bytes())} for m in imports],'prerequisite_actual_owner_observations':[{'name':n,'captured_actual_public_owners':byname.get(n,[])} for n in prereqs],'outstanding_exact_prerequisites':['TranscendentalNakamaye.Pending.CoefficientIdealRestriction.cosupport_coeff_subset','TranscendentalNakamaye.Pending.CoefficientIdeal.coeff_tower'],'standalone_compile_readiness':'NOT_CLAIMED: two direct original prerequisites absent captured base; await parent selected-support closure/integration. No dummy theorem or proof edit substitutes for them.','blueprint':{'fixed_revision':rev,'source_path':bp_path,'source_git_blob':blob(bp_path),'whole_source_sha256':sha(bpraw),'whole_capture':'maximal-contact-whole-original-fixed-native.tex.txt','complete_node_attachments':bprows,'direct_declaration_to_node':{'centresIn_of_isGeoTestTower_withN':'mc:restrict-tower','cosupp_coeff_withN':'mc:coefficient-restriction-support','isCoherent_coeffMarked':'mc:restrict-marked'},'coherence_written_proof_note':'mc:restrict-marked explicitly binds isCoherent_coeffMarked and states coherence but is a definition node with no separate proof. Preserve that complete original node; the actual proof invokes isAmbientFamily_derivMarked and IsAmbientFamily.isCoherent_msum, whose complete original mc:coefficient-ideal / mc:marked-finite-sum / mc:finite-sum node chain is captured with both written sum proofs. Do not invent a historical separate coherence proof or mark an external anchor as a retained proof.'},'relocation_verifier':str(verifier.relative_to(R)),'relocation_verifier_sha256':sha(verifier.read_bytes()),'proof_type_payload_edits':0,'administrative_changes':['Pure imports of existing immutable public modules','Standard release header','Frozen canonical namespace/open relocation only','Exact active Tower context and ALL three authentic scope closings retained'],'runtime_build_kernel_or_Expr_export_performed':False,'production_edits_performed':False,'git_mutations_performed':False}
(W/'plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
(W/'REPORT.md').write_text('''# Draft-only original coefficient restriction support\n\nThe draft contains exactly the three requested complete original declarations from fixed ordinary Git revision `'''+rev+'''`, with unchanged statement/proof bytes. The whole original source, each payload, the active options/universe/open/Tower variables, and the three balanced closings are captured separately.\n\nExisting immutable public imports supply the restriction definitions and actual coefficient ambient-family coherence data. Two genuine direct original prerequisites remain absent from the captured base: `cosupport_coeff_subset` and `CoefficientIdeal.coeff_tower`. They are reported for the parent's selected-support closure. This draft makes no compile-readiness or formal-gate claim.\n\nSix complete native blueprint nodes are retained in the audit attachment: the three direct nodes and the coefficient/marked-sum/finite-sum coherence chain. The direct coherence binding is in a definition node; its supporting original written finite-sum proofs are preserved rather than replaced by an external anchor or a new invented proof. Production currently retains only `mc:coefficient-ideal` among these exact labels; the plan records its actual node status separately.\n\nNo production source, root imports, Git state, existing Lean artifact, kernel gate, runtime or expression exporter was changed or run. Frontier remains the exclusive production integrator; canonical's separate source/context peer is pending.\n''')
manifest={p.name:sha(p.read_bytes()) for p in W.iterdir() if p.is_file() and p.name!='draft-fingerprints.json'}
(W/'draft-fingerprints.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'draft':str(out),'draft_sha256':sha(draft),'plan_sha256':sha((W/'plan.json').read_bytes()),'source_sha256':sha(raw),'bp_nodes':len(bprows),'written_proofs':sum(r['written_proof_count'] for r in bprows),'outstanding_exact_prerequisites':plan['outstanding_exact_prerequisites']},indent=2))
