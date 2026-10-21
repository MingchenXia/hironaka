"""Install the frozen additive Lean cohort independently of pending BP metadata.

All complete original written proofs are already captured in the peered handoffs.
This interim source pass does not claim final BP, build, kernel or Expr acceptance.
The full dual-cohort sync --additive40 --check is still a required final gate.
"""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
A=Path(__file__).resolve().parent;DST=A.parents[1];sys.dont_write_bytecode=True
sys.path.insert(0,str(DST/'scripts'));import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']]);flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
F=DST/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py';fn=next(n for n in ast.parse(F.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');scope={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(F),'exec'),scope);relocate=scope['relocate']
tree=ast.parse((A/'sync_frozen_sources.py').read_text());HEADER=ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='HEADER'for t in n.targets)))
sha=lambda b:hashlib.sha256(b).hexdigest()
initial=json.loads((A/'initial-port-plan.json').read_text());frozen=json.loads((A/'base323-frozen-before-additive40/immutable-base-source-and-kernel-parts.json').read_text())
def guards():
 for path,h in initial['existing_destination_math_source_digests'].items():assert sha((DST/path).read_bytes())==h,path
 for path,h in initial['toolchain_profiles'].items():assert sha((DST/path).read_bytes())==h,path
 for r in frozen['records']:
  assert sha((DST/r['source']).read_bytes())==r['source_sha256']
  for part in r['kernel_parts']:assert sha((DST/part['path']).read_bytes())==part['sha256']
guards()
from additive_frozen_cohort import Cohort
cohort=Cohort(A,DST,['git','-C','/workspace/archon-publish'],relocate,names,annotate,HEADER)
assert len(cohort.plan)==10 and sum(len(r['complete_original_declarations'])for r in cohort.plan)==40
changed=[]
def install(path,data,before=None):
 raw=data.encode()if isinstance(data,str)else data;dest=DST/path
 if dest.exists():
  old=dest.read_bytes()
  if old==raw:return
  candidates=before if isinstance(before,list)else[before];assert old in[x for x in candidates if x is not None],('Unapproved overwrite',path)
 else:old=None
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);changed.append({'path':path,'before_sha256':sha(old)if old is not None else None,'after_sha256':sha(raw)})
rows=cohort.sources(install);base=json.loads((A/'base323-frozen-before-additive40/provenance.json').read_text());allrows=base+rows;assert len(allrows)==373
(A/'provenance.json').write_text(json.dumps(allrows,indent=2)+'\n')
for filename,text in [('core-old-modules.tsv',''.join(r['source_module']+'\t'+r['destination_module']+'\n'for r in allrows)),('core-new-modules.tsv',''.join(r['destination_module']+'\t'+r['destination_module']+'\n'for r in allrows))]:(A/filename).write_text(text)
mods={p.relative_to(DST).as_posix().removesuffix('.lean').replace('/','.')for p in(DST/'Hironaka').rglob('*.lean')}|{'Hironaka'}
assert len(mods)==1159+373+1,len(mods)
imp=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',re.M);dag={m:set(imp.findall((DST/(m.replace('.','/')+'.lean')).read_text()))&mods for m in mods};seen=set();active=set()
def walk(m):
 if m in seen:return
 assert m not in active,('Import cycle',m);active.add(m)
 for d in dag[m]:walk(d)
 active.remove(m);seen.add(m)
walk('Hironaka');assert seen==mods,('Orphan physical modules',sorted(mods-seen))
(A/'all-standalone-modules.txt').write_text(''.join(m+'\n'for m in sorted(mods)))
guards()
report={'status':'ADDITIVE_SOURCES_INSTALLED_FINAL_BP_REPLAY_AND_ALL_RUNTIME_GATES_PENDING','base_fixed_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','additive_fixed_revision':'47cef49895832e3bfe492f66e1f2ac68785187dd','immutable_base_source_and_kernel_parts':323,'additive_whole_original_modules':40,'additional_support_files':10,'complete_original_support_declarations':40,'new_source_records':len(allrows),'actual_physical_source_modules_including_root':len(mods),'every_physical_source_module_reachable_from_root':True,'changed_sources':changed,'old1159_math_sources_and_frozen_profiles_unchanged':True,'written_type_or_proof_payload_edits':0,'build_kernel_Expr_BP_final_gate_claimed':False}
(A/'additive40-sources-only-install-receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
