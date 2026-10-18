"""Pin complete whole modules and every actual support root against entire parents."""
from pathlib import Path
import hashlib,json,subprocess,sys
A=Path(__file__).resolve().parent;ROOT=A.parents[1];SOURCE=Path('/workspace/archon-nakamaye-main');NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
REV='6a888f9dc4155b9ec1407b27223eb37218957159';BASE='827676fab01aea03c526b02e5cc13d57568c571d';sha=lambda raw:hashlib.sha256(raw).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
whole=json.loads((A/'provenance.json').read_text())+json.loads((A/'older-whole-source-provenance.json').read_text());assert len(whole)==16
support=json.loads((A/'original-support-source-provenance.json').read_text());assert len(support)==3
(A/'whole-provenance.json').write_text(json.dumps(whole,indent=2)+'\n')
snapshots=[]
for family,records in [('whole',whole),('support',support)]:
 for r in records:
  module=r['source_module']if family=='whole'else r['source_parent_module'];path=r['source_path']if family=='whole'else r['source_parent_path'];h=r['source_sha256']if family=='whole'else r['source_parent_sha256']
  raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+path]);assert sha(raw)==h and(NATIVE/(module.replace('.','/')+'.lean')).read_bytes()==raw
  assert sha((ROOT/r['destination_path']).read_bytes())==r['destination_sha256']
  snapshots.append({'family':family,'native_module':module,'native_source_sha256':h,'native_olean_sha256':sha((NATIVE/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')).read_bytes()),'public_module':r['destination_module'],'public_source_sha256':r['destination_sha256'],'public_olean_sha256':sha((ROOT/'.lake/build/lib/lean'/(r['destination_module'].replace('.','/')+'.olean')).read_bytes())})
(A/'strict-capture-source-and-kernel-snapshot.json').write_text(json.dumps(snapshots,indent=2)+'\n')
for filename,text in [('old-modules.tsv',''.join(r['source_module']+'\t'+r['destination_module']+'\n'for r in whole)),('new-modules.tsv',''.join(r['destination_module']+'\t'+r['destination_module']+'\n'for r in whole)),('fragment-old-modules.tsv',''.join(r['source_parent_module']+'\t'+r['destination_module']+'\n'for r in support)),('fragment-new-modules.tsv',''.join(r['destination_module']+'\t'+r['destination_module']+'\n'for r in support))]:(A/filename).write_text(text)
paths=subprocess.check_output(['git','-C',str(SOURCE),'ls-tree','-r','--name-only',REV,'--','TranscendentalNakamaye/TranscendentalNakamaye'],text=True).splitlines();modules=[p.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.')for p in paths if p.endswith('.lean')];normal={m:names.new_mod(m)for m in modules if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.'))}
previous='audit/surface-bennett-and-compact-ordered-curves-20261018/exact-module-renames.tsv';old_raw=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+previous]);assert(ROOT/previous).read_bytes()==old_raw
inherited={m:n for m,n in(line.split('\t')for line in old_raw.decode().splitlines())if n.startswith('Hironaka.Support.')};assert len(inherited)==4;normal.update(inherited)
(A/'exact-module-renames.tsv').write_text(''.join(m+'\t'+n+'\n'for m,n in normal.items()));fragment=dict(normal);fragment.update({r['source_parent_module']:r['destination_module']for r in support});(A/'fragment-exact-module-renames.tsv').write_text(''.join(m+'\t'+n+'\n'for m,n in fragment.items()))
profiles={'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean':'1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755','audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean':'49aba8c3a923533a210946026b6ac67556c82e79d0c603b10c5b15994cf055ab','audit/local-sharp-curves-20261015/compare_full_expr_dag.py':'28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'}
for path,h in profiles.items():assert sha((ROOT/path).read_bytes())==h,path
(A/'strict-frozen-tool-profiles.json').write_text(json.dumps(profiles,indent=2)+'\n');print(json.dumps({'whole_modules':16,'support_modules':3,'all_actual_public_support_roots_required':True,'full_native_parents_retained_unfiltered':True,'filters_or_waivers':0}))
