"""Independent source/BP/provenance-only peer. No Lean/build/export/production writes."""
from pathlib import Path
import ast,collections,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;FINAL='47cef49895832e3bfe492f66e1f2ac68785187dd';BASE='4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07';G='/workspace/archon-publish';sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',G,*args])
def blob(rev,p):return git('show',rev+':'+p)
def batch(rev,paths):
 ps=list(dict.fromkeys(paths));r=git('cat-file','--batch') if False else subprocess.check_output(['git','-C',G,'cat-file','--batch'],input=''.join(rev+':'+p+'\n' for p in ps).encode());pos=0;out={}
 for p in ps:
  end=r.index(b'\n',pos);h=r[pos:end].split();assert len(h)==3 and h[1]==b'blob',(p,h);n=int(h[2]);pos=end+1;out[p]=r[pos:pos+n];pos+=n+1
 assert pos==len(r);return out
frozen=D/'frozen-contracts';fp=json.loads((D/'input-fingerprints.json').read_text());fingerchecks={}
for rel,e in fp['standalone_frozen_inputs'].items():
 p=(D/'frozen-inputs'/rel.split('audit/canonical-elementary-family-and-local-producers-20261021/',1)[1]) if rel.startswith('audit/canonical-elementary-family-and-local-producers-20261021/') else (frozen/rel)
 if not p.exists():continue
 fingerchecks[rel]=sha(p.read_bytes())==e['sha256'];assert fingerchecks[rel],rel
spec=importlib.util.spec_from_file_location('peer_frozen_names',frozen/'scripts/upstream_namespace_map.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names);names.set_api_modules(['TranscendentalNakamaye.Pending.HironakaAPI'+s for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
code=(frozen/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py').read_text();fn=next(n for n in ast.parse(code).body if isinstance(n,ast.FunctionDef) and n.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),'FROZEN_RELOCATE_AST_ONLY','exec'),env);relocate=env['relocate']
sync=(D/'frozen-inputs/sync_frozen_sources.py').read_text();header=ast.literal_eval(next(n.value for n in ast.parse(sync).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='HEADER' for t in n.targets)))
spec=importlib.util.spec_from_file_location('peer_frozen_bp_scope',frozen/'scripts/upstream_blueprint_scope.py');bpm=importlib.util.module_from_spec(spec);spec.loader.exec_module(bpm)
external=json.loads((frozen/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((frozen/'scripts/upstream_blueprint_unbound_bindings.json').read_text());typography=json.loads((frozen/'scripts/upstream_blueprint_typography.json').read_text())
mods=json.loads((D/'module-provenance-plan.json').read_text());bps=json.loads((D/'blueprint-provenance-plan.json').read_text());roots=json.loads((D/'actual-root-name-relocations.json').read_text());bindings=json.loads((D/'literal-blueprint-bindings.json').read_text());assert len(mods)==len(bps)==40
finalmf=blob(FINAL,fp['fixed_final_manifest']['git_path']);basemf=blob(BASE,fp['fixed_excluded_five_manifest']['git_path']);assert sha(finalmf)==fp['fixed_final_manifest']['sha256'] and finalmf==(D/'fixed-manifests/final45.json').read_bytes();assert sha(basemf)==fp['fixed_excluded_five_manifest']['sha256'] and basemf==(D/'fixed-manifests/excluded5.json').read_bytes()
final=json.loads(finalmf);base=json.loads(basemf);fm={r['module']:r for r in final['modules']};bm={r['module']:r for r in base['modules']};assert len(fm)==45 and len(bm)==5 and set(x['source_module'] for x in mods)==set(fm)-set(bm)
files=batch(FINAL,[r[k]['path'] for r in fm.values() for k in ['source','blueprint']]+[r['independent_receipt_git_path'] for r in mods]);basepaths=set(git('ls-tree','-r','--name-only',BASE,'--','TranscendentalNakamaye/TranscendentalNakamaye').decode().splitlines());fiverows=[]
for m,r in bm.items():
 for k in ['source','blueprint']:
  path=r[k]['path'];assert blob(BASE,path)==files[fm[m][k]['path']];assert sha(files[fm[m][k]['path']])==r[k]['sha256']
 fiverows.append({'module':m,'whole_source_and_BP_identical_at_both_fixed_revisions':True})
rows=[];newroots=[];newbindings=[];proofs=[];hist=collections.Counter();all_imports=[]
for rec in mods:
 m=rec['source_module'];r=fm[m];raw=files[rec['source_path']];original=D/'original'/rec['source_path'];candidate=D/rec['candidate_path'];assert raw==original.read_bytes() and sha(raw)==rec['source_sha256']==r['source']['sha256'];assert rec['source_path'] not in basepaths
 expected=(header+relocate(raw.decode())).encode();actual=candidate.read_bytes();assert expected==actual and sha(actual)==rec['destination_sha256'];assert rec['destination_module']==names.new_mod(m);assert rec['proof_body_edits']==0 and not rec['administrative_context_edits'] and not rec['additional_support_imports']
 rr=files[rec['independent_receipt_git_path']];assert sha(rr)==rec['independent_receipt_sha256'] and rr==(D/'fixed-receipts'/(m+'.json')).read_bytes();receipt=json.loads(rr);assert len(receipt['actual_roots'])==rec['actual_root_observations']
 for root in receipt['actual_roots']:
  newroots.append({'owner_source_module':m,'owner_destination_module':names.new_mod(m),'source_name':root['name'],'candidate_name':names.rename_const(root['name']),'is_private':root['name'].startswith('_private.'),'transitive_axioms':root['transitive_axioms'],'evidence':rec['independent_receipt_git_path']});hist[', '.join(sorted(root['transitive_axioms'])) or '(none)']+=1
 bp=next(x for x in bps if x['module']==m);bpraw=files[bp['source_path']];bpactual=(D/bp['candidate_path']).read_bytes();assert bpraw==(D/'original'/bp['source_path']).read_bytes() and sha(bpraw)==bp['source_sha256']==r['blueprint']['sha256']
 text=names.rename_text_names(bpraw.decode()).replace('\\chapter{','\\section{')
 for adj in typography.get(Path(bp['destination_path']).name,[]):assert text.count(adj['before'])==1;text=text.replace(adj['before'],adj['after'])
 text=bpm.annotate(text,external,unbound);assert text.encode()==bpactual and sha(bpactual)==bp['destination_sha256'];originalproofs=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',bpraw.decode(),re.S);newproofs=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',text,re.S);assert len(originalproofs)==len(newproofs)==bp['proofs']
 for i,(old,new) in enumerate(zip(originalproofs,newproofs)):
  assert names.rename_text_names(old)==new
  proofs.append({'module':m,'proof':i,'whole_original_proof_sha256':sha(old.encode()),'whole_mapped_proof_sha256':sha(new.encode()),'complete_proof_retained':True})
 sb=[n.strip() for gr in re.findall(r'\\lean\{([^}]+)\}',bpraw.decode()) for n in gr.split(',')];db=[n.strip() for gr in re.findall(r'\\lean\{([^}]+)\}',text) for n in gr.split(',')];assert sb==bp['original_bindings'] and db==bp['local_bindings'] and len(sb)==len(db)
 for x,y in zip(sb,db):newbindings.append({'owner_module':m,'source_name':x,'candidate_name':y})
 assert len(re.findall(r'\\begin\{definition\}',text))==bp['definitions'];imports=re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',raw.decode(),re.M);mapped_imports=re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',actual.decode(),re.M);assert mapped_imports==[names.new_mod(x) if x.startswith('TranscendentalNakamaye.') else x for x in imports]
 all_imports.extend({'module':m,'source_import':x,'destination_import':y} for x,y in zip(imports,mapped_imports))
 rows.append({'module':m,'source_sha256':sha(raw),'candidate_sha256':sha(actual),'source_bytes':len(raw),'source_lines':len(raw.splitlines()),'whole_fixed_source_preserved_under_exact_frozen_recipe':True,'BP_source_sha256':sha(bpraw),'BP_candidate_sha256':sha(bpactual),'whole_fixed_BP_preserved_under_exact_frozen_recipe':True,'complete_written_proofs':len(originalproofs),'definition_nodes':bp['definitions'],'actual_roots_from_fixed_receipt':len(receipt['actual_roots']),'source_absent_fixed_base':True})
assert newroots==roots;assert newbindings==bindings;assert len(proofs)==122 and sum(x['definition_nodes'] for x in rows)==3;assert len(newroots)==712 and len(newbindings)==229
oldactual=json.loads((D/'frozen-inputs/support-prep/principal-parts/missing-prerequisite-preflight/old1159-actual-moduledata-names.json').read_text());baseactual=json.loads((D/'frozen-inputs/new-native-actual-name-inventory.json').read_text());supp=json.loads((D/'frozen-inputs/new-original-prerequisite-extracts/plan.json').read_text());known={}
for r in oldactual:
 for nm in r['actual_roots']:known.setdefault(nm,[]).append({'cohort':'old1159','module':r['module']})
for r in baseactual:
 for root in r['actual_roots']:known.setdefault(names.rename_const(root['original_name']),[]).append({'cohort':'base316','module':r['source_module']})
for r in supp:
 for nm in r['complete_original_declarations']:known.setdefault(names.rename_const(nm),[]).append({'cohort':'supplement13','module':r['destination_module']})
collisions=[{'root':r,'existing_owners':known[r['candidate_name']]} for r in roots if r['candidate_name'] in known];pre=json.loads((D/'collision-preflight.json').read_text());assert collisions==[{k:x[k] for k in ['root','existing_owners']} for x in pre['public_root_collisions']] and len(collisions)==4 and not pre['private_root_collisions'] and not pre['candidate_duplicate_names'];assert len({r['candidate_name'] for r in roots})==712
for x in collisions:
 r=x['root'];assert not r['is_private'];assert r['source_name'].rsplit('.',1)[-1] in ['eq_1','congr_simp'];assert not r['source_name'].startswith(r['owner_source_module']+'.')
(D/'static-peer-canonical-file-checks.json').write_text(json.dumps({'whole_source_and_BP_rows':rows,'whole_written_proof_checks':proofs,'excluded5_fixed_revision_checks':fiverows,'actual_root_relocations_reproduced':712,'literal_binding_relocations_reproduced':229,'fixed_contract_hash_checks':fingerchecks,'actual_collision_set_reproduced':collisions,'dependencies_literal_imports':all_imports,'actual_axiom_histogram_FROM_FIXED_RECEIPTS_ONLY':dict(hist),'no_runtime_or_production_edit':True},ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'static_status':'PASS_WHOLE_FIXED_SOURCE_BP_AND_ROOT_RELOCATION_CHECKS','sources':len(rows),'chapters':len(rows),'source_lines':sum(x['source_lines'] for x in rows),'proofs':len(proofs),'definitions':sum(x['definition_nodes'] for x in rows),'actual_roots_from_fixed_receipts':len(roots),'foreign_generated_helper_collisions':len(collisions),'dependency_revision_review':'PENDING_FINAL323_REPORT','proof_or_type_payload_replacement':False,'Lean_kernel_Expr_claimed':False}))
