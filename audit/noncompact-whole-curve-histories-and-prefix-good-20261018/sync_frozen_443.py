"""Replay complete accepted443 additions from ordinary published native Git.

Original blueprints are installed before Lean sources. The fixed namespace
relocation and two imports of already verified original support are recorded.
No type or proof tokens, instance contexts or canonical tools are changed here.
"""
from pathlib import Path
import argparse, ast, hashlib, json, re, subprocess, sys

sys.dont_write_bytecode = True
A = Path(__file__).resolve().parent
ROOT = A.parents[1]
REV = '6a888f9dc4155b9ec1407b27223eb37218957159'
BASE = '827676fab01aea03c526b02e5cc13d57568c571d'
CP = '4774cd3a97737754b463603a2188df4cd48efd84'
TREE = '5361620df281449c007c69f5ff5528d066259455'
PREFIX = 'TranscendentalNakamaye/audit/hironaka-subgoals-'
OLD_INV = PREFIX + '429-20261018/regular-main-v49-inventory.json'
INV = PREFIX + '443-20261018/regular-main-v50-inventory.json'
FROZEN = 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
HEADER = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
REPLACEMENTS = {
 'HironakaActualHSConstantCentreJetFrames': ('Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS', 'Hironaka.Support.OriginalFixedRealAmbientHSDictionaryExact'),
}
sha = lambda raw: hashlib.sha256(raw).hexdigest()

def main():
 p = argparse.ArgumentParser(description=__doc__)
 p.add_argument('--source-root', type=Path, default=Path('/workspace/archon-nakamaye-main'))
 p.add_argument('--check', action='store_true')
 args = p.parse_args()
 def show(path, rev=REV, source=args.source_root):
  return subprocess.check_output(['git', '-C', str(source), 'show', rev + ':' + path])
 def save(name, value):
  raw = (json.dumps(value, indent=2) + '\n').encode()
  if args.check: assert (A/name).read_bytes() == raw, name
  else: (A/name).write_bytes(raw)
 def install(path, raw, before=None):
  target = ROOT/path
  raw = raw.encode() if isinstance(raw,str) else raw
  if args.check: assert target.read_bytes() == raw, path
  elif target.exists():
   assert target.read_bytes() == raw or (before is not None and target.read_bytes() == before), ('Refuse overwrite',path)
   target.write_bytes(raw)
  else:
   target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(raw)
 guard=json.loads((A/'previous-public-source-digests.json').read_text())
 assert guard['previous_public_main']==BASE and len(guard['mathematical_sources'])==1140
 for path,h in guard['mathematical_sources'].items(): assert sha((ROOT/path).read_bytes())==h,path
 assert subprocess.check_output(['git','-C',str(args.source_root),'rev-parse',REV+':TranscendentalNakamaye'],text=True).strip()==TREE
 profiles=[FROZEN,'scripts/upstream_namespace_map.py','scripts/upstream_blueprint_scope.py','scripts/upstream_blueprint_external_bindings.json','scripts/upstream_blueprint_unbound_bindings.json','scripts/upstream_blueprint_typography.json']
 profile_hashes={}
 for path in profiles:
  raw=(ROOT/path).read_bytes();assert raw==show(path,BASE,ROOT),path;profile_hashes[path]=sha(raw)
 sys.path.insert(0,str(ROOT/'scripts'))
 import upstream_namespace_map as names
 from upstream_blueprint_scope import annotate
 names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
 flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
 frozen=(ROOT/FROZEN).read_text();function=next(n for n in ast.parse(frozen).body if isinstance(n,ast.FunctionDef)and n.name=='relocate')
 env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[function],type_ignores=[]),str(ROOT/FROZEN),'exec'),env);relocate=env['relocate']
 invraw=show(INV);oldraw=show(OLD_INV);inv=json.loads(invraw);old=json.loads(oldraw)
 modules=sorted(set(inv['modules'])-set(old['modules']));assert len(modules)==14
 bp_paths=sorted(set(inv['blueprint_paths'])-set(old['blueprint_paths']));assert len(bp_paths)==14
 src_index={r['module']:r for r in inv['source_records']};bp_index={r['path']:r for r in inv['blueprint_records']}
 external=json.loads((ROOT/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((ROOT/'scripts/upstream_blueprint_unbound_bindings.json').read_text());typography=json.loads((ROOT/'scripts/upstream_blueprint_typography.json').read_text())
 bindings=lambda text,kind='lean':[n.strip()for group in re.findall(r'\\'+kind+r'\{([^}]+)\}',text)for n in group.split(',')]
 bp_records=[]
 # Complete original source-facing blueprints precede all new Lean files.
 for path in bp_paths:
  raw=show(path);assert sha(raw)==bp_index[path]['sha256'],path
  text=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
  for change in typography.get(Path(path).name,[]):
   assert text.count(change['before'])==1;text=text.replace(change['before'],change['after'])
  text=annotate(text,external,unbound);dst='blueprint/'+Path(path).name
  assert not show('blueprint/extensions.tex',BASE,ROOT).decode().count('\\input{'+Path(dst).stem+'}')
  install(dst,text)
  bp_records.append({'published_source_revision':REV,'source_path':path,'source_sha256':sha(raw),'destination_path':dst,'destination_sha256':sha(text.encode()),'nodes':len(re.findall(r'\\label\{',text)),'proofs':text.count('\\begin{proof}'),'bindings':bindings(raw.decode()),'local_bindings':bindings(text),'upstream_bindings':bindings(text,'upstreamlean'),'unbound_upstream_bindings':bindings(text,'upstreamunbound')})
 old_master=show('blueprint/extensions.tex',BASE,ROOT);master=old_master.decode();old_inputs=re.findall(r'\\input\{([^}]+)\}',master);assert len(old_inputs)==601
 added_inputs=[Path(r['destination_path']).stem for r in bp_records];assert len(set(added_inputs))==14 and not set(added_inputs)&set(old_inputs)
 block=''.join('\\input{'+s+'}\n'for s in added_inputs);anchor='\\begin{thebibliography}{99}';assert master.count(anchor)==1
 master=master.replace(anchor,block+anchor);append_only_master=master;documentation_contexts=json.loads((A/'docs-master-documentation-contexts.json').read_text())if(A/'docs-master-documentation-contexts.json').exists()else[]
 for context in documentation_contexts:
  assert master.count(context['before'])==1;master=master.replace(context['before'],context['after'])
 install('blueprint/extensions.tex',master,old_master)
 records=[]
 for module in modules:
  rec=src_index[module];raw=show(rec['path']);assert sha(raw)==rec['sha256'],module
  destination=names.new_mod(module);path=destination.replace('.','/')+'.lean';assert path not in guard['mathematical_sources']
  output=initial=HEADER+relocate(raw.decode());contexts=[]
  if module.split('.')[-1] in REPLACEMENTS:
   before,after=REPLACEMENTS[module.split('.')[-1]];before='import '+before+'\n';after='import '+after+'\n';assert output.count(before)==1;output=output.replace(before,after)
   contexts.append({'kind':'pure_import_existing_verified_original_support','before':before,'after':after,'proof_and_type_tokens_changed':False})
  if module.split('.')[-1]=='HironakaSharpActualCurveGrowingGoodPreservation':
   before='import Hironaka.Resolution.HironakaSharpActualCurveLocallyFiniteSharpHistory\n';after='import Hironaka.Support.OriginalCentresOverAppendHeadExact\n'+before;assert output.count(before)==1;output=output.replace(before,after,1);contexts.append({'kind':'additional_pure_original_support_import','before':before,'after':after,'proof_and_type_tokens_changed':False})
  instance_contexts=json.loads((A/'original-instance-context-restorations.json').read_text()).get(destination,[])if(A/'original-instance-context-restorations.json').exists()else[]
  for context in instance_contexts:
   assert output.count(context['before'])==1;output=output.replace(context['before'],context['after'],1);contexts.append(context)
  install(path,output,initial.encode())
  records.append({'source_revision':CP,'published_source_revision':REV,'source_module':module,'source_path':rec['path'],'source_sha256':sha(raw),'destination_module':destination,'destination_path':path,'initial_synchronized_destination_sha256':sha(initial.encode()),'administrative_elaboration_contexts':contexts,'additional_pure_support_imports':[],'destination_sha256':sha(output.encode()),'cohort':'major443_delta','proof_edits':False})
 old_root=show('Hironaka.lean',BASE,ROOT);root=old_root.decode();marker=root.find('/-!');assert marker>=0
 added_imports=[r['destination_module']for r in records];assert all(('import '+m+'\n')not in root for m in added_imports)
 rootblock=''.join('import '+m+'\n\n'for m in added_imports);newroot=root[:marker]+rootblock+root[marker:];install('Hironaka.lean',newroot,old_root)
 for path,h in guard['mathematical_sources'].items():assert sha((ROOT/path).read_bytes())==h,path
 previous_bps=json.loads(show('audit/surface-bennett-and-compact-ordered-curves-20261018/blueprint-all-input-source-digests.json',BASE,ROOT))
 for path,h in previous_bps.items():
  if path!='blueprint/extensions.tex':assert sha((ROOT/path).read_bytes())==h,path
 save('frozen-major-extraction-plan.json',{'accepted_checkpoint':CP,'normal_published_revision':REV,'normal_published_project_tree':TREE,'previous_public_main':BASE,'source_inventory_path':INV,'source_inventory_sha256':sha(invraw),'previous_inventory_path':OLD_INV,'previous_inventory_sha256':sha(oldraw),'source_modules':modules,'source_blueprints':bp_paths,'excluded_later_source':True})
 save('provenance.json',records);save('blueprint-provenance.json',bp_records);save('new-local-bindings.json',sorted({n for r in bp_records for n in r['local_bindings']}));save('new-module-targets.json',added_imports)
 save('frozen-source-profile-sha256.json',{'profiles':profile_hashes,'relocate_function_source_sha256':sha(ast.get_source_segment(frozen,function).encode())})
 save('source-document-integration.json',{'root':{'path':'Hironaka.lean','before_sha256':sha(old_root),'after_sha256':sha(newroot.encode()),'added_imports':added_imports,'exact_inserted_block':rootblock},'master':{'path':'blueprint/extensions.tex','before_sha256':sha(old_master),'after_sha256':sha(master.encode()),'append_only_after_sha256':sha(append_only_master.encode()),'documentation_contexts':documentation_contexts,'before_inputs':601,'after_inputs':master.count('\\input{'),'added_inputs':[Path(r['destination_path']).stem for r in bp_records],'exact_inserted_block':block},'old_1140_mathematical_sources_preserved':True,'old_601_blueprint_chapter_sources_preserved':True})
 for filename,content in [('core-old-modules.tsv',''.join(r['source_module']+'\t'+r['destination_module']+'\n'for r in records)),('core-new-modules.tsv',''.join(r['destination_module']+'\t'+r['destination_module']+'\n'for r in records))]:
  if args.check:assert(A/filename).read_text()==content
  else:(A/filename).write_text(content)
 receipt={'status':'PASS_EXACT_NORMAL_GIT_SOURCE_AND_BLUEPRINT_REPLAY'if args.check else'COMPLETE_ORIGINAL_SOURCE_AND_BLUEPRINTS_COPIED','whole_modules':14,'blueprints':14,'nodes':sum(r['nodes']for r in bp_records),'proof_environments':sum(r['proofs']for r in bp_records),'local_bindings':len({n for r in bp_records for n in r['local_bindings']}),'old_math_sources_byte_identical':1140,'old_blueprint_chapter_sources_byte_identical':601,'original_type_or_proof_token_edits':0,'pure_import_replacements':1,'additional_pure_original_support_imports':1,'declaration_local_original_instance_restorations':sum(c['kind']=='declaration_local_recovery_of_original_compiled_instance_route'for r in records for c in r['administrative_elaboration_contexts']),'compiled_or_expression_checked_here':False,'normal_published_revision':REV,'private_ledger_required':False}
 if not args.check:save('source-sync-receipt.json',receipt)
 print(json.dumps(receipt))

if __name__=='__main__':main()
