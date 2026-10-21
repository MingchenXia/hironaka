#!/usr/bin/env python3
from pathlib import Path
import ast,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
R=Path('/workspace/archon-nakamaye');D=Path('/workspace/hironaka');N=R/'TranscendentalNakamaye';W=Path(__file__).resolve().parent
A=D/'audit/phase4-semantic-producers-20261021';A.mkdir(exist_ok=True)
G=['git',f'--git-dir={R}/.archon-horizon/vcs/workspace.git',f'--work-tree={R}'];REV=subprocess.check_output(G+['rev-parse','6446c03085'],text=True).strip();h=lambda b:hashlib.sha256(b).hexdigest()
base=D/'audit/canonical-elementary-family-and-local-producers-20261021'
spec=importlib.util.spec_from_file_location('names',D/'scripts/upstream_namespace_map.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names);names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])');fp=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(x for x in ast.parse(fp.read_text()).body if isinstance(x,ast.FunctionDef)and x.name=='relocate');e={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(fp),'exec'),e)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
mods=(W/'native6-modules.txt').read_text().splitlines()+['TranscendentalNakamaye.Pending.HironakaSharpActualDynamicIncidentHistory'];order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m);raw=subprocess.check_output(G+['show',REV+':TranscendentalNakamaye/'+m.replace('.','/')+'.lean']).decode()
 for dep in re.findall(r'^import (TranscendentalNakamaye[\w.]*)',raw,re.M):
  if dep in mods:visit(dep)
  else:assert (D/(names.new_mod(dep).replace('.','/')+'.lean')).is_file(),('Missing module-path prerequisite',dep)
 order.append(m)
for m in mods:visit(m)
rows=[];bps=[];alltex=list((N/'blueprint/src').glob('*.tex'));rawdir=A/'original-whole-source-captures';rawdir.mkdir(exist_ok=True)
extra={'Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms':['Hironaka.Support.AnalyticSubsetPresentationsExact'],'Hironaka.Resolution.HironakaCompactOpenBlowupExtension':['Hironaka.Support.AnalyticSubsetPresentationsExact']}
for m in order:
 sp='TranscendentalNakamaye/'+m.replace('.','/')+'.lean';raw=subprocess.check_output(G+['show',REV+':'+sp]);assert raw==(R/sp).read_bytes(),sp
 dm=names.new_mod(m);dst=dm.replace('.','/')+'.lean';assert not (D/dst).exists(),dst
 out=header+e['relocate'](raw.decode());initial=h(out.encode());extras=extra.get(dm,[])
 if extras:
  at=re.search(r'^import ',out,re.M).start();out=out[:at]+''.join('import '+x+'\n'for x in extras)+out[at:]
 capture=rawdir/(m+'.lean.txt');capture.write_bytes(raw)
 rows.append({'source_revision':REV,'source_module':m,'source_path':sp,'source_sha256':h(raw),'destination_module':dm,'destination_path':dst,'initial_synchronized_destination_sha256':initial,'destination_sha256':h(out.encode()),'administrative_elaboration_contexts':[],'additional_pure_support_imports':extras,'original_proof_tokens_changed':False,'whole_original_source_preserved':True,'raw_capture':str(capture.relative_to(A))})
 matches=[]
 for bp in alltex:
  if re.search(r'\\lean\{[^}]*'+re.escape(m)+r'\.',bp.read_text()):matches.append(bp)
 assert len(matches)==1,(m,matches)
 bp=matches[0];bsp='TranscendentalNakamaye/'+str(bp.relative_to(N));rawbp=subprocess.check_output(G+['show',REV+':'+bsp]);assert rawbp==bp.read_bytes(),bsp
 b=rawbp.decode();assert '\\notready'not in b,bsp;outbp=names.rename_text_names(b).replace('\\chapter{','\\section{');bcap=rawdir/(bp.name+'.txt');bcap.write_bytes(rawbp)
 bps.append({'source_revision':REV,'source_path':bsp,'source_sha256':h(rawbp),'destination_path':'blueprint/'+bp.name,'destination_sha256':h(outbp.encode()),'proofs':b.count('\\begin{proof}'),'definitions':b.count('\\begin{definition}'),'local_bindings':sorted(set(n.strip()for group in re.findall(r'\\lean\{([^}]+)\}',outbp)for n in group.split(','))),'whole_original_chapter_preserved':True,'proof_text_edits':0,'raw_capture':str(bcap.relative_to(A))})
assert len(rows)==len(bps)==7 and sum(x['proofs']for x in bps)==22
for fn,obj in [('provenance.json',rows),('blueprint-provenance.json',bps),('additional-pure-support-imports.json',extra)]: (A/fn).write_text(json.dumps(obj,indent=2)+'\n')
oldmath={str(p.relative_to(D)):h(p.read_bytes())for p in (D/'Hironaka').rglob('*.lean')};assert len(oldmath)==1532
oldbp={str(p.relative_to(D)):h(p.read_bytes())for p in (D/'blueprint').rglob('*.tex')};assert len(oldbp)==970
profiles=json.loads((base/'initial-port-plan.json').read_text())['toolchain_profiles'];assert all(h((D/p).read_bytes())==v for p,v in profiles.items())
(A/'fixed373-before-Hironaka.lean').write_bytes((D/'Hironaka.lean').read_bytes());(A/'fixed373-before-extensions.tex').write_bytes((D/'blueprint/extensions.tex').read_bytes())
guard={'standalone_base_revision':subprocess.check_output(['git','-C',str(D),'rev-parse','HEAD'],text=True).strip(),'authoring_ledger_revision':REV,'ordinary_published_revision':None,'old_mathematical_files':oldmath,'old_blueprint_files_including_master':oldbp,'frozen_profiles':profiles,'fixed373_verification_sha256':h((base/'final373-verification.json').read_bytes()),'source_modules':7,'BP_chapters':7,'new_written_proofs':22,'source_pin_kind':'ACCEPTED_LEDGER_AUTHORING_ONLY_ORDINARY_PUBLIC_REPLAY_PENDING','deferred_prior_modules_preserved_absent':['Hironaka/Resolution/HironakaOriginalGlobalOffZero.lean','Hironaka/Resolution/HironakaOriginalGlobalProperModification.lean']}
(A/'cohort-plan.json').write_text(json.dumps(guard,indent=2)+'\n');(A/'source-source-revision.txt').write_text(REV+'\n')
print(json.dumps({'status':'PREPARED_SEVEN_WHOLE_MODULES_BP_FIRST_INSTALL_PENDING','revision':REV,'A':str(A),'sources':7,'chapters':7,'proofs':22,'old_math_guard':1532,'old_TeX_guard':970,'pure_support_imports':extra},indent=2))
