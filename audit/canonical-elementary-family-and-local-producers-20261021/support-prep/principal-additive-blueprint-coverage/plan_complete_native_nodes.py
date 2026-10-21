from pathlib import Path
import hashlib,json,re,subprocess,sys,difflib
R=Path('/workspace/hironaka');A=R/'audit/canonical-elementary-family-and-local-producers-20261021';W=A/'support-prep/principal-additive-blueprint-coverage';U=Path('/workspace/archon-publish')
P=Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication');rev='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
roster_path=P/'native8-recursive-callee-closure/ordinary-source-declarations-by-parent.json';roster=json.loads(roster_path.read_text())
selected={x['actual_original_declaration']:x for p in roster for x in p['complete_ordinary_original_declarations']};assert len(roster)==10 and len(selected)==40
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
oldguard=json.loads((A/'initial-port-plan.json').read_text())['existing_blueprint_tex_digests'];oldguard.pop('blueprint/extensions.tex',None);assert len(oldguard)==619
newprovenance=json.loads((A/'blueprint-provenance.json').read_text());assert len(newprovenance)==349
newset={r['destination_path'] for r in newprovenance}
public={str(p.relative_to(R)):p.read_text() for p in (R/'blueprint').rglob('*.tex')}
# Exact documentary comparison strips ONLY original/local binding and verification status commands.
metadata=re.compile(r'\\(?:lean|upstreamlean|upstreamunbound)\{[^}]*\}|\\(?:leanok|mixedleanok|upstreamleanok|historicalleanok)\b')
def mathematical_body(s):return metadata.sub('',s)
node_start=re.compile(r'\\begin\{(definition|lemma|theorem|proposition|corollary|remark|convention)\}')
def nodes(s):
 matches=list(node_start.finditer(s));out=[]
 for i,m in enumerate(matches):
  stop=matches[i+1].start() if i+1<len(matches) else len(s)
  kind=m[1];k='\\end{'+kind+'}';coreend=s.index(k,m.end())+len(k)
  # Some native definition facts have explanatory proof prose OUTSIDE a proof environment.
  if re.match(r'\s*\\begin\{proof\}',s[coreend:stop]):coreend=s.index('\\end{proof}',coreend)+len('\\end{proof}')
  if coreend<len(s) and s[coreend]=='\n':coreend+=1
  end=stop
  section=re.search(r'^\\(?:sub)*section\b|^\\chapter\b',s[coreend:stop],re.M)
  if section:end=coreend+section.start()
  # Native entire trailing explanation retained; trim only separator blank lines.
  while end>coreend and s[end-1]=='\n' and s[end-2:end]=='\n\n':end-=1
  core=s[m.start():coreend];whole=s[m.start():end]
  labels=re.findall(r'\\label\{([^}]+)\}',core)
  if not labels:continue
  out.append({'labels':labels,'kind':kind,'start':m.start(),'coreend':coreend,'end':end,'core':core,'whole':whole,'bindings':[x.strip() for v in re.findall(r'\\lean\{([^}]+)\}',core) for x in v.split(',')],'all_bindings_with_kind':[{'macro':a,'binding':x.strip()} for a,v in re.findall(r'\\(lean|upstreamlean|upstreamunbound)\{([^}]+)\}',core) for x in v.split(',')],'uses':[x.strip() for v in re.findall(r'\\uses\{([^}]+)\}',core) for x in v.split(',')]})
 return out
publicnodes={};anchors={}
for path,s in public.items():
 for n in nodes(s):
  for label in n['labels']:publicnodes.setdefault(label,[]).append((path,n))
 for label in re.findall(r'\\label\{([^}]+)\}',s):anchors.setdefault(label,[]).append(path)
# No Lean runtime: all statuses below reuse already captured name observations and native witnesses.
basepath=P/'native40-callee-preflight/base-actual-name-observations.json';base=json.loads(basepath.read_text());baseowners={}
for r in base:baseowners.setdefault(r['actual_name'],[]).append(r['module'])
newrootpath=P/'native40-callee-preflight/native40-actual-physical-roots.json';newrows=json.loads(newrootpath.read_text())
# The metadata file's list records use native names; inspect schema rather than assume all root labels.
if isinstance(newrows,dict):newrows=newrows.get('roots',newrows.get('observations',newrows.get('actual_roots',[])))
newnames=set()
for row in newrows:
 if isinstance(row,str):newnames.add(names.rename_text_names(row))
 else:
  for k in ['name','actual_name','native_name','root','declaration']:
   if k in row and isinstance(row[k],str):newnames.add(names.rename_text_names(row[k]));break
# Existing text file is exact exported actual native40 names, canonicalized by the established map.
newnames.update((P/'native40-callee-preflight/planned40-public-actual-names.txt').read_text().splitlines())
nativeinvpath=A/'native-blueprint-original-binding-inventory.json';nativeinv={r['original_binding']:r for r in json.loads(nativeinvpath.read_text())}
wholeparents={};native_nodes=[]
for fn in ['maximal-contact.tex','hironaka.tex','blowup-calculus.tex']:
 source='TranscendentalNakamaye/blueprint/src/'+fn
 raw=subprocess.check_output(['git','-C',str(U),'show',rev+':'+source]);s=raw.decode();(W/(fn+'.whole-original.txt')).write_bytes(raw)
 oid=subprocess.check_output(['git','-C',str(U),'rev-parse',rev+':'+source]).decode().strip()
 wholeparents[fn]={'source_path':source,'revision':rev,'git_blob':oid,'sha256':sha(raw),'capture':fn+'.whole-original.txt'}
 for n in nodes(s):n.update(parent=fn,source=source);native_nodes.append(n)
selected_nodes=[n for n in native_nodes if any(b in selected for b in n['bindings'])]
covered={b for n in selected_nodes for b in n['bindings'] if b in selected};assert covered==set(selected)
assert len(selected_nodes)==22
# Additional complete original proof chain captures are optional foundations, never silently installed.
optional_labels=['hir:order-power','mc:normal-taylor-model','mc:normal-taylor-order']
optional=[n for n in native_nodes if any(l in optional_labels for l in n['labels'])]
assert len(optional)==3
records=[];attachment_table=[];mapping=[];primary=[];retained=[]
for n in selected_nodes+optional:
 label=n['labels'][0];parent=wholeparents[n['parent']];is_optional=label in optional_labels
 slug=label.replace(':','--')
 corefile=slug+'.complete-original-core.tex.txt';wholefile=slug+'.complete-original-node-with-native-prose.tex.txt'
 (W/corefile).write_text(n['core']);(W/wholefile).write_text(n['whole'])
 canonical=names.rename_text_names(n['core']);local=[]
 for path,pn in publicnodes.get(label,[]):
  # Full original statement/proof text compared, not merely a label or proof count.
  same=mathematical_body(canonical)==mathematical_body(pn['core'])
  local.append({'path':path,'cohort':'old619' if path in oldguard else ('new349' if path in newset else 'other_documentation'),'whole_file_sha256':sha(public[path]),'node_sha256':sha(pn['core']),'written_proofs':pn['core'].count('\\begin{proof}'),'entire_statement_and_proof_equal_after_only_namespace_and_attachment_status_relocation':same,'original_attachments_not_rewritten':True})
  if not same:
   (W/(slug+'.retained-comparison.diff.txt')).write_text(''.join(difflib.unified_diff(mathematical_body(canonical).splitlines(True),mathematical_body(pn['core']).splitlines(True),fromfile='canonical-original-core',tofile=path)))
 existing=any(x['entire_statement_and_proof_equal_after_only_namespace_and_attachment_status_relocation'] for x in local)
 status='ALREADY_RETAINED_COMPLETE_ORIGINAL_WRITTEN_PROOF_NO_DUPLICATE' if existing else ('OPTIONAL_FOUNDATION_COMPLETE_PROOF_NOT_SELECTED_FOR_AUTOMATIC_INSTALL' if is_optional else 'NEEDS_COMPLETE_ORIGINAL_NODE_ADDITION')
 bindings=[]
 for native in n['bindings']:
  publicname=names.rename_text_names(native)
  if publicname in baseowners:classification='EXISTING_ACTUAL_PUBLIC_BASE_NAME';evidence={'owners':baseowners[publicname],'source':str(basepath)}
  elif native in selected:classification='SELECTED_EXACT_ORIGINAL_SUPPORT_PENDING_LOCAL_GATES';evidence={'actual_native_parent':next(r['actual_native_parent'] for r in roster if any(d['actual_original_declaration']==native for d in r['complete_ordinary_original_declarations'])),'source':str(roster_path)}
  elif publicname in newnames:classification='ADDITIVE40_ACTUAL_NATIVE_ROOT_PENDING_LOCAL_GATES';evidence={'source':str(newrootpath)}
  else:classification='ORIGINAL_NATIVE_ONLY_ATTACHMENT_REQUIRES_EXPLICIT_UPSTREAM_STATUS_OR_ADDITIONAL_ACTUAL_PUBLIC_WITNESS';evidence={'existing_original_witness':nativeinv.get(native),'source':str(nativeinvpath)}
  row={'node_label':label,'native_name':native,'canonical_public_name':publicname,'classification':classification,'evidence':evidence};bindings.append(row);attachment_table.append(row)
 rec={'label':label,'all_labels':n['labels'],'role':'optional_foundation' if is_optional else 'direct_closed40_attachment','source_parent':parent,'native_start_line':(W/parent['capture']).read_text().count('\n',0,n['start'])+1,'native_core_end_line':(W/parent['capture']).read_text().count('\n',0,n['coreend']),'native_full_end_line':(W/parent['capture']).read_text().count('\n',0,n['end']),'environment':n['kind'],'core_capture':corefile,'core_sha256':sha(n['core']),'full_node_with_native_trailing_prose_capture':wholefile,'full_node_sha256':sha(n['whole']),'original_trailing_explanatory_prose_preserved':n['whole']!=n['core'],'written_proofs':n['core'].count('\\begin{proof}'),'selected_support_declarations':[b for b in n['bindings'] if b in selected],'all_original_attachments':bindings,'uses':n['uses'],'retained_complete_nodes':local,'external_anchor_paths':[p for p in anchors.get(label,[]) if p not in [x['path'] for x in local]],'classification':status}
 records.append(rec)
 if existing:retained.append(label)
 elif not is_optional:primary.append(label)
 for b in n['bindings']:
  if b in selected:mapping.append({'native_name':b,'canonical_public_name':names.rename_text_names(b),'node_label':label,'node_classification':status,'core_capture':corefile,'all_attachments_preserved':True})
# Snapshot each currently available support manifest, without mutating it or pretending later arrivals are present.
folders={'CoefficientIdeal':'defect-additive-coefficient-ideal','CoefficientIdealRestriction':'principal-additive-coefficient-restriction/complete-five','CoefficientRestrictionTower':'setup-additive-coefficient-tower','DerivativeIdealTower':'tangent-additive-derivative-tower','DropMembers':'defect-additive-drop-members','MarkedIdealOperationsTransform':'canonical-additive-marked-operations','MemberInterTowerAlong':'tangent-additive-member-inter','NormalDerivativeChart':'setup-additive-normal-derivative','OrderMultiplicativity':'setup-additive-order-powers','RestrictEmptyTower':'root-additive-empty-tower'}
folderrows=[]
for r in roster:
 short=r['actual_native_parent'].rsplit('.',1)[1];folder=A/'support-prep'/folders[short];files=[]
 if folder.exists():
  for q in sorted(folder.glob('*')):
   if q.is_file() and (q.suffix in ['.json','.md','.lean'] or 'node' in q.name):files.append({'path':str(q),'sha256':sha(q.read_bytes())})
 folderrows.append({'native_parent':r['actual_native_parent'],'selected_count':len(r['complete_ordinary_original_declarations']),'expected_folder':str(folder),'folder_exists_at_snapshot':folder.exists(),'captured_current_manifest_node_files':files,'draft_frozen_and_peer_status':'NOT_INFERRED_BY_THIS_BP_PLAN; consult author/peer receipts'})
# Definition-support proof obligations must not be converted into invented tiny nodes.
definition_chains=[{'node':'mc:restrict-marked','selected_fact':'isCoherent_coeffMarked','original_status':'definition states coherence and attaches the theorem; no separate written proof environment','complete_original_supporting_nodes':['mc:coefficient-ideal','mc:marked-finite-sum','mc:finite-sum'],'all_supporting_nodes_already_in_primary_selection':True},{'node':'mc:coefficient-ideal','selected_fact':'derivMarked_zero','original_status':'literal definition/same derivative-marked data; actual derivative ambient-family gives coefficient summands','complete_original_supporting_nodes':['mc:derivative-marked','mc:marked-finite-sum','mc:finite-sum'],'all_supporting_nodes_already_in_primary_selection':True},{'node':'mc:derivative-marked','selected_facts':['controlledTransform_le_of_le','cosupp_subset_cosupp_derivMarked'],'original_status':'definition is followed by genuine original explanatory monotonicity/iterated Giraud proof prose outside a proof environment','original_trailing_prose_capture':'mc--derivative-marked.complete-original-node-with-native-prose.tex.txt','written_dependency_nodes_retained_as_references':['hir:giraud-support'],'no_new_proof_invented':True},{'node':'mc:flat-chart','selected_fact':'FlatChart.nd_nil','original_status':'definition contains actual chart/inverse/normal-derivative data; nd_nil is a literal immediate identity. It has no original separate written proof environment','complete_original_selected_derivative_proof_node':'mc:normal-derivative-ideal','optional_complete_normal_power_dictionary_chain':['mc:normal-taylor-model','mc:normal-taylor-order'],'no_rfl_micro_node_invented':True}]
plan={'status':'READ_ONLY_COMPLETE_ORIGINAL_BP_INTEGRATION_PLAN_NO_PRODUCTION_OR_RUNTIME','revision':rev,'ordinary_source_repository':str(U),'selected_support_parent_count':10,'selected_ordinary_declarations':40,'selected_roster':str(roster_path),'selected_roster_sha256':sha(roster_path.read_bytes()),'old619_guard_source':str(A/'initial-port-plan.json'),'old619_count':len(oldguard),'new349_provenance_sha256':sha((A/'blueprint-provenance.json').read_bytes()),'new349_count':len(newprovenance),'complete_original_source_parents':wholeparents,'direct_node_count':len(selected_nodes),'direct_written_proof_count':sum(n['core'].count('\\begin{proof}') for n in selected_nodes),'direct_existing_full_nodes_no_duplicate':[l for l in retained if l not in optional_labels],'minimal_direct_new_complete_nodes':primary,'minimal_direct_new_node_count':len(primary),'minimal_direct_new_written_proofs':sum(r['written_proofs'] for r in records if r['label'] in primary),'proposed_new_excerpt_chapter_groups':{'NEW maximal-contact support excerpt':[r['label'] for r in records if r['label'] in primary and r['source_parent']['source_path'].endswith('/maximal-contact.tex')],'NEW hironaka support excerpt':[r['label'] for r in records if r['label'] in primary and r['source_parent']['source_path'].endswith('/hironaka.tex')]},'optional_foundation_nodes':optional_labels,'definition_support_chains':definition_chains,'support_draft_snapshots':folderrows,'node_records':records,'all_40_declaration_attachments':mapping,'all_original_attachments_preserved':True,'attachment_observations':len(attachment_table),'attachment_status_counts':{k:sum(r['classification']==k for r in attachment_table) for k in sorted({r['classification'] for r in attachment_table})},'root_decisions_required':['Install only chosen NEW excerpt chapters and add inputs; never overwrite old619/new349 chapters.','Promote any existing external anchor for a newly selected complete node without duplicate label definitions; preserve its original historical reference evidence.','Classify every original lean attachment using actual public owner/binding gates. Selected support names remain pending until their real gates; native-only attachments retain explicit upstream status and existing actual native witness, never vanish.','Optional foundation captures are a bounded proof-chain choice, not an automatic transitive expansion of all uses; all remaining genuine dependencies remain explicit references.'],'runtime_build_kernel_or_Expr_export_performed':False,'production_source_blueprint_or_git_edits':False,'strict_math_or_binding_acceptance_claimed':False}
(W/'complete-original-node-integration-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
(W/'all-original-lean-attachment-mappings.json').write_text(json.dumps(attachment_table,ensure_ascii=False,indent=2)+'\n')
(W/'closed40-declaration-node-map.json').write_text(json.dumps(mapping,ensure_ascii=False,indent=2)+'\n')
(W/'minimal-new-node-list.txt').write_text('\n'.join(primary)+'\n')
print(json.dumps({'direct_nodes':len(selected_nodes),'already_retained':plan['direct_existing_full_nodes_no_duplicate'],'minimum_new_nodes':len(primary),'minimum_new_proofs':plan['minimal_direct_new_written_proofs'],'groups':plan['proposed_new_excerpt_chapter_groups'],'all_attachment_status_counts':plan['attachment_status_counts'],'draft_folders_present':sum(r['folder_exists_at_snapshot'] for r in folderrows),'plan_sha256':sha((W/'complete-original-node-integration-plan.json').read_bytes())},ensure_ascii=False,indent=2))
