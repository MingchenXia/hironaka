"""Reproduce this whole increment using ordinary public Git and frozen relocation."""
from pathlib import Path
import argparse, ast, hashlib, json, re, subprocess, sys
P=argparse.ArgumentParser();P.add_argument('--source-root',type=Path,required=True);args=P.parse_args()
A=Path(__file__).resolve().parent;D=A.parents[1]
sys.path.insert(0,str(D/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
reference=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
node=next(x for x in ast.parse(reference.read_text()).body if isinstance(x,ast.FunctionDef) and x.name=='relocate')
exec(compile(ast.Module(body=[node],type_ignores=[]),str(reference),'exec'))
sha=lambda b:hashlib.sha256(b).hexdigest()
plan=json.loads((A/'cohort-plan.json').read_text());revision=plan['ordinary_native_source_revision'];base=plan['standalone_base_revision']
def show(path):return subprocess.check_output(['git','-C',str(args.source_root),'show',revision+':'+path])
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
for path,h in plan['frozen_profiles'].items():assert sha((D/path).read_bytes())==h,path
rows=json.loads((A/'provenance.json').read_text());extras=json.loads((A/'additional-pure-support-imports.json').read_text())
assert len(rows)==14
for rec in rows:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_sha256']
 assert raw==(A/rec['raw_capture']).read_bytes()
 output=header+relocate(raw.decode());assert sha(output.encode())==rec['initial_synchronized_destination_sha256']
 for x in rec['administrative_elaboration_contexts']:
  assert output.count(x['before'])==1;output=output.replace(x['before'],x['after'])
 imports=rec['additional_pure_support_imports'];assert imports==extras.get(rec['destination_module'],[])
 if imports:
  first=re.search(r'^import ',output,re.M);output=output[:first.start()]+''.join('import '+m+'\n' for m in imports)+output[first.start():]
 actual=(D/rec['destination_path']).read_bytes();assert actual==output.encode() and sha(actual)==rec['destination_sha256'],rec['destination_module']
bps=json.loads((A/'blueprint-provenance.json').read_text())
external=json.loads((D/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((D/'scripts/upstream_blueprint_unbound_bindings.json').read_text());typography=json.loads((D/'scripts/upstream_blueprint_typography.json').read_text())
assert len(bps)==14
for rec in bps:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_sha256'] and raw==(A/rec['raw_capture']).read_bytes()
 output=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
 for x in typography.get(Path(rec['destination_path']).name,[]):
  assert output.count(x['before'])==1;output=output.replace(x['before'],x['after'])
 output=annotate(output,external,unbound)
 actual=(D/rec['destination_path']).read_bytes();assert actual==output.encode() and sha(actual)==rec['destination_sha256'],rec['destination_path']
 assert output.count('\\begin{proof}')==rec['proofs']
supports=json.loads((A/'new-support-provenance.json').read_text());assert len(supports)==8
for rec in supports:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_parent_sha256']
 fragment=(A/rec['raw_capture']).read_bytes();assert sha(fragment)==rec['source_complete_declaration_sha256'] and raw.count(fragment)==1
 actual=(D/rec['destination_path']).read_bytes();assert sha(actual)==rec['destination_sha256'] and actual.count(relocate(fragment.decode()).encode())==1
for key in ['old_mathematical_files','old_blueprint_files_including_master']:
 for path,h in plan[key].items():
  if path=='blueprint/extensions.tex':continue
  assert sha((D/path).read_bytes())==h,path
assert sha((D/'README.md').read_bytes())==plan['README_sha256']
oldroot=subprocess.check_output(['git','-C',str(D),'show',base+':Hironaka.lean']).decode();root=(D/'Hironaka.lean').read_text()
for rec in rows:
 line='import '+rec['destination_module']+'\n';assert root.count(line)==1;root=root.replace(line,'',1)
assert root==oldroot
oldmaster=subprocess.check_output(['git','-C',str(D),'show',base+':blueprint/extensions.tex']).decode();master=(D/'blueprint/extensions.tex').read_text()
for rec in bps:
 line='\\input{'+Path(rec['destination_path']).stem+'}\n';assert master.count(line)==1
 assert master.index(line)<master.index('\\end{document}');master=master.replace(line,'',1)
assert master==oldmaster
receipt={'status':'PASS_EXACT_PUBLISHED_SOURCE_REPLAY_AND_OLD_SOURCE_GUARDS','source_revision':revision,'standalone_base':base,'complete_whole_modules':14,'complete_chapters':14,'complete_written_proofs':sum(r['proofs'] for r in bps),'geometric_definitions':sum(r['definitions'] for r in bps),'complete_original_support_declarations':8,'support_modules':3,'old_math_files_unchanged':len(plan['old_mathematical_files']),'old_blueprints_unchanged':len(plan['old_blueprint_files_including_master'])-1,'README_unchanged':True,'root_changes_only_fourteen_imports':True,'blueprint_master_only_fourteen_inputs_before_end_document':True,'private_ledger_required':False}
(A/'published-source-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
