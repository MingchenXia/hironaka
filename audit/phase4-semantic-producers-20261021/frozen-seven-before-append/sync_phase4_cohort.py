#!/usr/bin/env python3
"""Whole original ordinary-Git cohort, blueprint first, unchanged frozen relocation."""
from pathlib import Path
import argparse,ast,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent;D=A.parents[1];h=lambda b:hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--source-root',type=Path,required=True);p.add_argument('--revision',default='52e93b1998d2bff0e24251c92d0dd6f7d882e3e0');p.add_argument('--check',action='store_true');args=p.parse_args();assert re.fullmatch('[0-9a-f]{40}',args.revision)
git=['git','-C',str(args.source_root)];assert subprocess.check_output(git+['rev-parse',args.revision],text=True).strip()==args.revision
plan=json.loads((A/'cohort-plan.json').read_text());rows=json.loads((A/'provenance.json').read_text());bps=json.loads((A/'blueprint-provenance.json').read_text())
for path,want in plan['old_mathematical_files'].items():assert h((D/path).read_bytes())==want,path
for path,want in plan['old_blueprint_files_including_master'].items():
 if path!='blueprint/extensions.tex':assert h((D/path).read_bytes())==want,path
for path,want in plan['frozen_profiles'].items():assert h((D/path).read_bytes())==want,path
for path in plan['deferred_prior_modules_preserved_absent']:assert not (D/path).exists(),path
sys.path.insert(0,str(D/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])');frozen=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(x for x in ast.parse(frozen.read_text()).body if isinstance(x,ast.FunctionDef)and x.name=='relocate');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'),env)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
def original(row):
 raw=subprocess.check_output(git+['show',args.revision+':'+row['source_path']]);assert h(raw)==row['source_sha256'];assert raw==(A/row['raw_capture']).read_bytes();return raw.decode()
def install(path,out):
 data=out.encode();target=D/path
 if target.exists():
  actual=target.read_bytes()
  if actual!=data:
   approvals=json.loads((A/'approved-before-sources.json').read_text())if(A/'approved-before-sources.json').exists()else{}
   eligible=[]
   for item in approvals.get(path,[]):
    b=(A/item['path']).read_bytes();assert h(b)==item['sha256'];eligible.append(b)
   assert not args.check and actual in eligible,('Refuse to overwrite prior source',path)
   target.write_bytes(data)
 else:
  assert not args.check,('Missing synchronized file',path);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
# Complete source-facing original statements and written proofs are installed FIRST.
for row in bps:
 out=names.rename_text_names(original(row)).replace('\\chapter{','\\section{');assert h(out.encode())==row['destination_sha256'];assert out.count('\\begin{proof}')==row['proofs'];install(row['destination_path'],out)
for row in rows:
 out=header+env['relocate'](original(row));assert h(out.encode())==row['initial_synchronized_destination_sha256']
 extras=row['additional_pure_support_imports']
 if extras:
  assert all((D/(m.replace('.','/')+'.lean')).exists()for m in extras);at=re.search(r'^import ',out,re.M).start();out=out[:at]+''.join('import '+m+'\n'for m in extras)+out[at:]
 for adj in row['administrative_elaboration_contexts']:assert out.count(adj['before'])==1;out=out.replace(adj['before'],adj['after'])
 assert h(out.encode())==row['destination_sha256'];install(row['destination_path'],out)
oldroot=(A/'fixed373-before-Hironaka.lean').read_text();at=oldroot.index('/-!');newroot=oldroot[:at]+''.join('import '+r['destination_module']+'\n'for r in rows)+'\n'+oldroot[at:]
oldmaster=(A/'fixed373-before-extensions.tex').read_text();at=oldmaster.rindex('\\end{document}');newmaster=oldmaster[:at]+''.join('\\input{'+Path(b['destination_path']).stem+'}\n'for b in bps)+oldmaster[at:]
for path,before,after in [('Hironaka.lean',oldroot,newroot),('blueprint/extensions.tex',oldmaster,newmaster)]:
 current=(D/path).read_text();assert current in [before,after],('Unexpected root/master modification',path)
 if args.check:assert current==after,path
 elif current!=after:(D/path).write_text(after)
receipt={'status':'PASS_FIXED_ORDINARY_GIT_WHOLE_SOURCE_AND_BP_REPLAY','ordinary_source_revision':args.revision,'accepted_authoring_ledger':plan['authoring_ledger_revision'],'fixed_standalone_base':plan['standalone_base_revision'],'new_modules':len(rows),'complete_original_chapters':len(bps),'new_written_proofs':sum(r['proofs']for r in bps),'all_old_mathematical_sources_byte_unchanged':len(plan['old_mathematical_files']),'all_old_TeX_files_preserved':len(plan['old_blueprint_files_including_master'])-1,'existing_master_separately_append_only':True,'four_frozen_profiles_unchanged':True,'proof_type_payload_edits':0,'only_new_source_and_BP_files_written':True,'source_roster_sha256':h((A/'provenance.json').read_bytes()),'BP_roster_sha256':h((A/'blueprint-provenance.json').read_bytes()),'build_kernel_Expr_covered_here':False}
(A/'source-replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
