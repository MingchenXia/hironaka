"""Synchronize only the accepted 333-minus-322 original whole-source increment.

Normal published Git is the sole source; existing mathematical files are guarded.
The preceding canonical relocation function and namespace/profile files are unchanged.
"""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
SOURCE=Path('/workspace/archon-nakamaye-publish')
REV='d9c39cb76c09fb9c5c92936fb96d61e8547c08b3'
CHECKPOINT='429ae0ee718cdae5faace3f7aecb6eedf23bb81e'
BASE='f7985b63b43a2423dfbf09b3eef4e487330dde1d'
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda n:json.loads((HERE/n).read_text())
plan=load('frozen-extraction-plan.json');guard=load('previous-public-source-digests.json')
assert plan['checkpoint']==CHECKPOINT and plan['published_revision']==REV
assert len(plan['modules'])==len(plan['blueprint_paths'])==11
for f,d in guard['mathematical_sources'].items():assert sha((ROOT/f).read_bytes())==d,f
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['','2','3','4']])
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
function=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[function],type_ignores=[]),str(frozen),'exec'))
show=lambda f:subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+f])
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
prior={r['destination_module']:r for r in load('provenance.json')} if (HERE/'provenance.json').exists() else {}
contexts=load('owned-administrative-contexts.json') if (HERE/'owned-administrative-contexts.json').exists() else {}
imports=load('additional-pure-support-imports.json') if (HERE/'additional-pure-support-imports.json').exists() else {}
records=[]
for m in plan['modules']:
    src='TranscendentalNakamaye/'+m.replace('.','/')+'.lean';raw=show(src);newm=names.new_mod(m)
    p=ROOT/(newm.replace('.','/')+'.lean');out=header+relocate(raw.decode());initial=sha(out.encode())
    for adjustment in contexts.get(newm,[]):
        assert out.count(adjustment['before'])==1
        out=out.replace(adjustment['before'],adjustment['after'])
    first=re.search(r'^import ',out,re.M);assert first
    out=out[:first.start()]+''.join('import '+x+'\n' for x in imports.get(newm,[]))+out[first.start():]
    if p.exists():
        assert newm in prior and sha(p.read_bytes())==prior[newm]['destination_sha256'],('Refuse existing-source overwrite',p)
    else:p.parent.mkdir(parents=True,exist_ok=True)
    assert not (ROOT/(newm.replace('.','/')+'.lean')).as_posix().endswith('/Hironaka.lean')
    if not p.exists() or p.read_text()!=out:p.write_text(out)
    records.append({'source_revision':CHECKPOINT,'published_source_revision':REV,'source_module':m,'source_path':src,'source_sha256':sha(raw),'destination_module':newm,'initial_synchronized_destination_sha256':initial,'additional_pure_support_imports':imports.get(newm,[]),'administrative_elaboration_contexts':contexts.get(newm,[]),'destination_sha256':sha(out.encode())})
(HERE/'provenance.json').write_text(json.dumps(records,indent=2)+'\n')
(HERE/'old-modules.tsv').write_text(''.join(r['source_module']+'\t'+r['destination_module']+'\n' for r in records))
(HERE/'new-modules.tsv').write_text(''.join(r['destination_module']+'\t'+r['destination_module']+'\n' for r in records))
support_records=load('new-support-provenance.json') if (HERE/'new-support-provenance.json').exists() else []
(HERE/'new-module-targets.json').write_text(json.dumps([r['destination_module'] for r in records]+list(dict.fromkeys(r['destination_module'] for r in support_records)),indent=2)+'\n')
root=ROOT/'Hironaka.lean';oldroot=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':Hironaka.lean'],text=True)
rootlines=''.join('import '+names.new_mod(m)+'\n\n' for m in plan['leaf_roots'])
marker=oldroot.find('/-!');assert marker>=0
newroot=oldroot[:marker]+rootlines+oldroot[marker:]
assert root.read_text() in (oldroot,newroot),'Root differs beyond owned 4 imports'
if root.read_text()!=newroot:root.write_text(newroot)
external=json.loads((ROOT/'scripts/upstream_blueprint_external_bindings.json').read_text())
unbound=json.loads((ROOT/'scripts/upstream_blueprint_unbound_bindings.json').read_text())
typography=json.loads((ROOT/'scripts/upstream_blueprint_typography.json').read_text())
oldbps={r['destination_path']:r for r in load('blueprint-provenance.json')} if (HERE/'blueprint-provenance.json').exists() else {}
bps=[]
for src in plan['blueprint_paths']:
    raw=show(src);out=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
    p=ROOT/'blueprint'/Path(src).name
    for adjustment in typography.get(p.name,[]):
        assert out.count(adjustment['before'])==1
        out=out.replace(adjustment['before'],adjustment['after'])
    out=annotate(out,external,unbound);rel=str(p.relative_to(ROOT))
    if p.exists():assert rel in oldbps and sha(p.read_bytes())==oldbps[rel]['destination_sha256'],('Refuse existing blueprint overwrite',p)
    if not p.exists() or p.read_text()!=out:p.write_text(out)
    bindings=lambda text,kind:[s.strip() for g in re.findall(r'\\'+kind+r'\{([^}]+)\}',text) for s in g.split(',')]
    bps.append({'source_path':src,'source_sha256':sha(raw),'destination_path':rel,'destination_sha256':sha(out.encode()),'nodes':len(re.findall(r'\\label\{',out)),'proofs':out.count('\\begin{proof}'),'bindings':bindings(raw.decode(),'lean'),'local_bindings':bindings(out,'lean'),'upstream_bindings':bindings(out,'upstreamlean'),'unbound_upstream_bindings':bindings(out,'upstreamunbound')})
assert sum(r['proofs'] for r in bps)==21
bindings=sorted({x for r in bps for x in r['local_bindings']});assert len(bindings)==38
(HERE/'blueprint-provenance.json').write_text(json.dumps(bps,indent=2)+'\n')
(HERE/'new-local-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
master=ROOT/'blueprint/extensions.tex';oldmaster=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':blueprint/extensions.tex'],text=True)
needle='\\begin{thebibliography}{99}';assert oldmaster.count(needle)==1
newmaster=oldmaster.replace(needle,''.join('\\input{'+Path(r['destination_path']).stem+'}\n' for r in bps)+needle)
master_with_added_inputs=newmaster
for change in load('master-documentation-contexts.json') if (HERE/'master-documentation-contexts.json').exists() else []:
 assert newmaster.count(change['before'])==1
 newmaster=newmaster.replace(change['before'],change['after'])
assert master.read_text() in (oldmaster,master_with_added_inputs,newmaster),'Master document differs beyond owned11 inputs and recorded documentation scope'
if master.read_text()!=newmaster:master.write_text(newmaster)
mods=subprocess.check_output(['git','-C',str(SOURCE),'ls-tree','-r','--name-only',REV,'--','TranscendentalNakamaye/TranscendentalNakamaye'],text=True).splitlines()
mods=[p.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.') for p in mods if p.endswith('.lean')]
(HERE/'exact-module-renames.tsv').write_text(''.join(m+'\t'+names.new_mod(m)+'\n' for m in mods if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.'))))
print(json.dumps({'status':'COPIED_COMPLETE_FROZEN_ORIGINAL_SOURCE','whole_modules':len(records),'blueprint_chapters':len(bps),'complete_original_proofs':sum(r['proofs'] for r in bps),'local_bindings':len(bindings),'root_imports':len(plan['leaf_roots']),'previous_mathematical_sources_guarded':len(guard['mathematical_sources'])}))
