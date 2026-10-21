"""Draft-only complete original CoefficientRestrictionTower complement.
No Lean, build, kernel, Expr, production or Git mutations.
"""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
O=Path(__file__).resolve().parent;A=O.parents[1];R=A.parents[1]
REV='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07';SRC='TranscendentalNakamaye/TranscendentalNakamaye/Pending/CoefficientRestrictionTower.lean';BP='TranscendentalNakamaye/blueprint/src/maximal-contact.tex'
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(O/'CoefficientRestrictionTower.original.lean.txt').read_bytes();text=raw.decode();bpraw=(O/'maximal-contact.original.tex.txt').read_bytes();bp=bpraw.decode()
assert subprocess.check_output(['git','-C','/workspace/archon-publish','show',REV+':'+SRC])==raw
assert subprocess.check_output(['git','-C','/workspace/archon-publish','show',REV+':'+BP])==bpraw
blob=subprocess.check_output(['git','-C','/workspace/archon-publish','rev-parse',REV+':'+SRC],text=True).strip();bpblob=subprocess.check_output(['git','-C','/workspace/archon-publish','rev-parse',REV+':'+BP],text=True).strip()
sys.path.insert(0,str(R/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=R/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'),env);relocate=env['relocate']
reused={'vanishesToOrderOn_of_isInSpanOnAt','isInSpanAt_comp_map','FlatChart.holomorphicAt_nd'}
records=[]
for m in re.finditer(r'^(theorem|def)\s+([^\s(]+)',text,re.M):
 start=text.rfind('/--',0,m.start());assert start>=0 and text.index('-/',start)<m.start()
 end=m.end()+re.search(r'\n\n(?=(?:/--|/-!|(?:end|section)\b))',text[m.end():]).start()+1
 payload=text[start:end];assert text.count(payload)==1
 rec={'kind':m.group(1),'short_name':m.group(2),'native_name':'TranscendentalNakamaye.Pending.CoefficientRestrictionTower.'+m.group(2),'start_character':start,'end_character':end,'start_byte':len(text[:start].encode()),'end_byte':len(text[:end].encode()),'start_line':text.count('\n',0,start)+1,'end_line':text.count('\n',0,end),'sha256':sha(payload.encode()),'complete_original_payload':payload,'already_existing_public_helper':m.group(2)in reused}
 records.append(rec)
assert len(records)==15 and sum(r['already_existing_public_helper']for r in records)==3
selected=[r for r in records if not r['already_existing_public_helper']];assert len(selected)==12
old=R/'Hironaka/MarkedIdeal/CoefficientRestrictionTower.lean';oldraw=old.read_bytes()
for r in records:
 if r['already_existing_public_helper']:assert oldraw.decode().count(relocate(r['complete_original_payload']))==1,r['short_name']
# Keep the whole original command/section structure; only imported duplicate declarations and original import lines are removed.
imp_end=re.match(r'(?:import [^\n]+\n)+',text).end()
removed=[(0,imp_end)]+[(r['start_character'],r['end_character'])for r in records if r['already_existing_public_helper']]
def retained_context(lo,hi):
 pieces=[];pos=lo
 for a,b in sorted(removed):
  if b<=pos or a>=hi:continue
  if pos<a:pieces.append((pos,min(a,hi)))
  pos=max(pos,b)
 if pos<hi:pieces.append((pos,hi))
 return pieces
layout=[]
head='/- Complete original CoefficientRestrictionTower complement; provisional dependency closure. -/\nimport Hironaka.MarkedIdeal.CoefficientRestrictionTower\n'
layout.append({'canonical_administrative_context':head,'sha256':sha(head.encode()),'kind':'Pure import of frozen original owner; no supplied certificate or proof alias.'})
pos=0
for i,r in enumerate(selected):
 for a,b in retained_context(pos,r['start_character']):
  rawctx=text[a:b];ctx=relocate(rawctx)
  layout.append({'canonical_administrative_context':ctx,'sha256':sha(ctx.encode()),'original_context_start_byte':len(text[:a].encode()),'original_context_end_byte':len(text[:b].encode()),'original_context_sha256':sha(rawctx.encode())})
 layout.append({'original_payload_index':i});pos=r['end_character']
for a,b in retained_context(pos,len(text)):
 rawctx=text[a:b];ctx=relocate(rawctx);layout.append({'canonical_administrative_context':ctx,'sha256':sha(ctx.encode()),'original_context_start_byte':len(text[:a].encode()),'original_context_end_byte':len(text[:b].encode()),'original_context_sha256':sha(rawctx.encode())})
chunks=[r['complete_original_payload']for r in selected]
out=''.join(relocate(chunks[x['original_payload_index']])if'original_payload_index'in x else x['canonical_administrative_context']for x in layout)
# Lexical section stack checks preserve every named and anonymous original closing.
def section_trace(src):
 stack=[];trace=[]
 for num,line in enumerate(src.splitlines(),1):
  if re.match(r'^(?:noncomputable )?section(?: |$)',line):
   name=line.split('section',1)[1].strip();stack.append(('section',name));trace.append([num,'open',name or'(anonymous)'])
  elif line.startswith('namespace '):
   name=line.removeprefix('namespace ').strip();stack.append(('namespace',name));trace.append([num,'open namespace',name])
  elif re.match(r'^end(?: |$)',line):
   name=line[3:].strip();assert stack,(num,line);kind,opened=stack.pop();assert not name or name==opened,(num,line,opened);trace.append([num,'close',opened or'(anonymous)'])
 assert not stack,stack
 return trace
original_scope=section_trace(text);draft_scope=section_trace(out)
assert sum(a[1]=='open'for a in original_scope)==sum(a[1]=='open'for a in draft_scope)==6
f=O/'CoefficientRestrictionTowerIffOriginalExact.lean';assert not f.exists();f.write_text(out)
for r in selected:
 p=O/'selected-original-payloads'/Path(r['short_name']+'.lean.txt');p.parent.mkdir(exist_ok=True);assert not p.exists();p.write_text(r['complete_original_payload'])
node_records=[]
for label in ['mc:normal-coefficient-invariant','mc:normal-coefficient-step','mc:coefficient-restriction-full']:
 index=bp.index('\\label{'+label+'}');start=bp.rfind('\\begin{lemma}',0,index);end=bp.index('\\end{proof}',index)+len('\\end{proof}');node=bp[start:end]+'\n'
 p=O/(label.replace(':','--')+'.complete-original-node.tex.txt');assert not p.exists();p.write_text(node)
 bindings=[n.strip()for group in re.findall(r'\\lean\{([^}]+)\}',node)for n in group.split(',')]
 node_records.append({'label':label,'capture':p.name,'start_line':bp.count('\n',0,start)+1,'end_line':bp.count('\n',0,end)+1,'start_byte':len(bp[:start].encode()),'end_byte_exclusive_before_added_terminal_newline':len(bp[:end].encode()),'complete_original_node_sha256':sha(node.encode()),'complete_written_proofs':1,'all_original_bindings':bindings,'original_uses':[n.strip()for g in re.findall(r'\\uses\{([^}]+)\}',node)for n in g.split(',')],'statement_and_proof_edits':0,'public_complete_node_present_at_draft':any(('\\label{'+label+'}')in q.read_text()for q in(R/'blueprint').glob('*.tex'))})
allbindings=[n for row in node_records for n in row['all_original_bindings']];assert len(allbindings)==15 and set(allbindings)=={r['native_name']for r in records}
active_commands=[]
for m in re.finditer(r'^(?:set_option|open|universe|namespace|noncomputable section|variable|section|end|include|omit|local instance|attribute)\b[^\n]*(?:\n[ \t]+[^\n]*)*',text,re.M):
 active_commands.append({'start_line':text.count('\n',0,m.start())+1,'end_line':text.count('\n',0,m.end())+1,'complete_original_command':m.group(),'sha256':sha(m.group().encode())})
audit={'status':'DRAFT_ONLY_COMPLETE_ORIGINAL_SAME_PARENT_CHAIN_PROVISIONAL_PENDING_ACTUAL_METADATA_CLOSURE','fixed_ordinary_revision':REV,'source_path':SRC,'source_git_blob':blob,'whole_original_source_sha256':sha(raw),'draft_path':f.name,'draft_sha256':sha(out.encode()),'draft_lines':len(out.splitlines()),'destination_module':'Hironaka.Support.CoefficientRestrictionTowerIffOriginalExact','primary_requested_native_declaration':'TranscendentalNakamaye.Pending.CoefficientRestrictionTower.coeff_restrict_tower_iff','selected_complete_declarations':12,'complete_original_declarations':[r['native_name']for r in selected],'selected_payloads':selected,'original_payload_chunks':chunks,'original_selected_source':'\n'.join(chunks),'original_selected_sha256':sha('\n'.join(chunks).encode()),'canonical_source_layout':layout,'original_context_commands_including_all_sections':active_commands,'original_section_scope_trace':original_scope,'draft_section_scope_trace':draft_scope,'all_named_and_anonymous_closings_balanced':True,'original_universe':'u','all_original_active_open_variable_include_local_instance_section_contexts_preserved':True,'original_reused_helpers':[r for r in records if r['already_existing_public_helper']],'frozen_original_owner_import':{'module':'Hironaka.MarkedIdeal.CoefficientRestrictionTower','path':str(old.relative_to(R)),'sha256':sha(oldraw),'all_three_complete_original_reused_payloads_found_exactly':True},'blueprint':{'source_path':BP,'fixed_git_blob':bpblob,'whole_original_source_sha256':sha(bpraw),'complete_original_nodes':node_records,'all_original_bindings_retained':15,'selected12_and_reused3_covered':True,'original_binding_classification_deferred_to_actual_owner_availability':True},'mathematical_statement_or_proof_edits':0,'old1159_sources_or_old619_chapters_edited':False,'production_Git_Lean_kernel_Expr_invocations':False,'actual_recursive_callee_closure_confirmed':False,'pending':'Canonical actual-CI closure must confirm the selected same-parent set and outside-parent dependencies before any installation. No local elaboration, kernel, expression, or publication PASS is claimed.'}
p=O/'extraction-audit.json';assert not p.exists();p.write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
print(f,sha(f.read_bytes()),len(out.splitlines()));print(p,sha(p.read_bytes()));print('selected',','.join(r['short_name']for r in selected));print('BP nodes',[r['label']for r in node_records])
