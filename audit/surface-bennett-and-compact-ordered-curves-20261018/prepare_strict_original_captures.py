"""Pin all actual new public roots and unchanged original whole-module inputs."""
from pathlib import Path
import hashlib,json,subprocess,sys
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
SOURCE=Path('/workspace/archon-nakamaye-main')
NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
REV='07d2a1e3242cc2c37bab1d8eab4847246555c8eb'
BASE='964b18f9c1cf70c263f4d4351b826413450ddf74'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
records=json.loads((A/'provenance.json').read_text());assert len(records)==34
snapshots=[]
for r in records:
 raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+r['source_path']])
 assert sha(raw)==r['source_sha256']
 assert (NATIVE/(r['source_module'].replace('.','/')+'.lean')).read_bytes()==raw
 assert sha((ROOT/r['destination_path']).read_bytes())==r['destination_sha256']
 native=NATIVE/'.lake/build/lib/lean'/(r['source_module'].replace('.','/')+'.olean')
 public=ROOT/'.lake/build/lib/lean'/(r['destination_module'].replace('.','/')+'.olean')
 snapshots.append({'family':'whole','native_module':r['source_module'],'native_source_sha256':r['source_sha256'],'native_olean_sha256':sha(native.read_bytes()),'public_module':r['destination_module'],'public_source_sha256':r['destination_sha256'],'public_olean_sha256':sha(public.read_bytes())})
(A/'strict-capture-source-and-kernel-snapshot.json').write_text(json.dumps(snapshots,indent=2)+'\n')
paths=subprocess.check_output(['git','-C',str(SOURCE),'ls-tree','-r','--name-only',REV,'--','TranscendentalNakamaye/TranscendentalNakamaye'],text=True).splitlines()
modules=[p.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.')for p in paths if p.endswith('.lean')]
normal={m:names.new_mod(m)for m in modules if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.'))}
# These already published, strict-verified original support owners are the
# actual public owners of complete original prerequisites; preserve their map.
old_path='audit/zero-dimensional-centre-bennett-and-actual-global-histories-20261018/exact-module-renames.tsv'
old_raw=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+old_path])
assert (ROOT/old_path).read_bytes()==old_raw
old=dict(line.split('\t')for line in old_raw.decode().splitlines())
support_owners={m:n for m,n in old.items()if n.startswith('Hironaka.Support.')}
assert len(support_owners)==4,support_owners
normal.update(support_owners)
(A/'exact-module-renames.tsv').write_text(''.join(m+'\t'+n+'\n'for m,n in normal.items()))
(A/'inherited-exact-support-owner-mapping.json').write_text(json.dumps({'previous_public_main':BASE,'pinned_mapping_path':old_path,'pinned_mapping_sha256':sha(old_raw),'owners':support_owners,'old_support_source_changed':False},indent=2)+'\n')
profiles={
 'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean':'1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755',
 'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean':'49aba8c3a923533a210946026b6ac67556c82e79d0c603b10c5b15994cf055ab',
 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py':'28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'}
for p,h in profiles.items():assert sha((ROOT/p).read_bytes())==h,p
(A/'strict-frozen-tool-profiles.json').write_text(json.dumps(profiles,indent=2)+'\n')
print(json.dumps({'whole_modules':len(records),'new_support_modules':0,'all_actual_moduleData_roots_required':True,'root_filters':0,'original_type_or_proof_edits':0}))
