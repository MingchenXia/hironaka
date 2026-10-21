#!/usr/bin/env python3
"""Bounded final ready-module groups through UNCHANGED V3; complete per-owner captures.

At most eight pairs per reader invocation. Original parents already captured
are reused byte-for-byte when all original inputs remain exact. A documented
actual-owner correction alone may request a necessary narrow original recapture.
"""
from pathlib import Path
import gzip,hashlib,json,os,subprocess,threading,time,argparse,re
A=Path(__file__).resolve().parent;ROOT=A.parents[1];NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
p=argparse.ArgumentParser();p.add_argument('--build-pid',type=int,required=True);p.add_argument('--build-log',type=Path,required=True);args=p.parse_args()
PROBE='/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh'
EXPORTER=ROOT/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
V2=ROOT/'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean';COMPARATOR=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
profiles=json.loads((A/'initial-port-plan.json').read_text())['toolchain_profiles']
for f in [EXPORTER,V2,COMPARATOR]:assert sha(f)==profiles[str(f.relative_to(ROOT))],f
rows=json.loads((A/'provenance.json').read_text());OUT=A/'final-per-module-expressions';STATE=OUT/'status.json'
state=json.loads(STATE.read_text());state['batch_invocation_bound']=8;state['frozen_exporter_modified']=False
public_modules={x['destination_module']for x in rows}
state['modules']={m:r for m,r in state['modules'].items()if m in public_modules}
state['whole_module_scope_partition']='../canonical-elementary-family-and-local-producers-20261021/deferred-complete-module-partition.json'
state['status']='RUNNING_ACTUAL_NEW_ROOT_FULL_EXPRESSION_GATE';state['total_new_modules']=len(rows)
PROFILE=A/'new-actual-callee-owner-profiles.json';ownerprofiles=json.loads(PROFILE.read_text())if PROFILE.exists()else{}
COMPANIONS=A/'new-original-companion-owner-modules.json';companions=json.loads(COMPANIONS.read_text())if COMPANIONS.exists()else{}
WITNESSES=A/'new-original-verbatim-root-witnesses.json';witnesses=json.loads(WITNESSES.read_text())if WITNESSES.exists()else{}
def artifacts(root,m):
 p=root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean');return [{'path':str(q),'sha256':sha(q),'bytes':q.stat().st_size}for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server')]if q.exists()]
def save():STATE.write_text(json.dumps(state,indent=2)+'\n')
def valid(row):
 r=state['modules'].get(row['destination_module'],{});profile=ownerprofiles.get(row['destination_module'])
 return r.get('capture_exit')==0 and r.get('scoped_comparison_complete')is True and r.get('actual_callee_owner_profile')==profile and r.get('original_owner_modules',[row['source_module']])==[row['source_module'],*companions.get(row['destination_module'],{}).get('source_modules',[])] and r.get('actual_original_witness_spec')==witnesses.get(row['destination_module']) and all(Path(x['path']).exists()and sha(Path(x['path']))==x['sha256']for x in r.get('frozen_inputs',[]))
def compare_one(rec,folder):
 oldplain=folder/'original-unfiltered.jsonl';newplain=folder/'public-unfiltered.jsonl'
 for side,dest in [('original-unfiltered',oldplain),('public-unfiltered',newplain)]:
  with gzip.open(ROOT/rec['captures'][side]['path'],'rb')as inp,dest.open('wb')as out:
   for line in inp:out.write(line)
  assert sha(dest)==rec['captures'][side]['uncompressed_sha256']
 def compare(orig,name):
  report=folder/(name+'.json');cmd=['python3',str(COMPARATOR),str(orig),str(newplain),str(report)]
  with(folder/(name+'.log')).open('w')as log:r=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
  d=json.loads(report.read_text());return {'exit_code':r.returncode,'report':str(report.relative_to(ROOT)),'report_sha256':sha(report),'status':d['status'],'actual_public_roots':d['native']['all_actual_constants'],'original_roots_compared':d['old']['all_actual_constants'],'entire_theorem_proofs_exact':sum(x['theorem_proofs_exact']for x in d['module_counts'].values()),'missing':d['missing'],'extra':d['native_extras'],'difference_roots':sorted({x['constant'][1]for x in d['differences']})}
 rec['raw_complete_parent_comparison']=compare(oldplain,'raw-complete-parent-comparison')
 if rec['copy_kind']=='whole_original_module':rec['every_actual_new_root_comparison']=rec['raw_complete_parent_comparison']
 else:
  names=set(rec['captures']['public-unfiltered']['actual_root_names']);found=set();discarded=[];selected=folder/'original-selected-verbatim-for-all-public-roots.jsonl'
  forced={};spec=witnesses.get(rec['destination_module'])
  if spec:
   source=ROOT/spec['capture']['path'];assert sha(source)==spec['capture']['gzip_sha256']
   with gzip.open(source,'rb')as inp:
    for line in inp:
     d=json.loads(line)
     if d['name']in spec['actual_original_root_names']:assert d['module']==rec['destination_module'];forced[d['name']]=line
   assert set(forced)==set(spec['actual_original_root_names'])
   rec['verbatim_old_foreign_original_witnesses']={'spec':spec,'rows_modified':False,'all_source_capture_rows_retained':True}
  with oldplain.open('rb')as inp,selected.open('wb')as out:
   for line in inp:
    d=json.loads(line)
    if d['name']in names:
     found.add(d['name'])
     if d['name']not in forced:out.write(line)
    else:discarded.append(d['name'])
   for line in forced.values():out.write(line)
  assert found==names,('Actual new public root missing from original',rec['destination_module'],names-found)
  if rec['copy_kind']=='pure_existing_support_imports':assert not names
  rec['original_parent_selection']={'source_capture':rec['captures']['original-unfiltered']['path'],'selected_original_rows_sha256':sha(selected),'all_actual_public_roots_retained':True,'selected_rows_modified':False,'original_parent_roots_already_reused_from_preceding_support':discarded,'original_parent_roots_unfiltered_in_raw_capture':True}
  rec['every_actual_new_root_comparison']=compare(selected,'all-actual-new-complement-root-comparison');selected.unlink()
 rec['scoped_comparison_complete']=True;oldplain.unlink();newplain.unlink()
def capture_group(group):
 assert 1<=len(group)<=8
 serial=1
 while(A/'final-expression-batches'/('batch'+str(serial))).exists():serial+=1
 batch=A/'final-expression-batches'/('batch'+str(serial));batch.mkdir(parents=True)
 recs={};folders={};originals=[]
 for row in group:
  m=row['destination_module'];old=row['source_module'];folder=OUT/m;attempt=1
  while(folder/('attempt'+str(attempt))).exists():attempt+=1
  folder=folder/('attempt'+str(attempt));folder.mkdir(parents=True);folders[m]=folder
  ns=NATIVE/(old.replace('.','/')+'.lean');ps=ROOT/row['destination_path'];assert sha(ns)==row['source_sha256']and sha(ps)==row['destination_sha256'],('Source drift',m)
  assert artifacts(NATIVE,old)and artifacts(ROOT,m)
  extraowners=companions.get(m,{}).get('source_modules',[])
  ins=[{'path':str(ns),'sha256':sha(ns)},{'path':str(ps),'sha256':sha(ps)},*artifacts(NATIVE,old),*artifacts(ROOT,m)]
  for owner in extraowners:
   source=NATIVE/(owner.replace('.','/')+'.lean');expected=next(r['source_sha256']for r in rows if r['source_module']==owner);assert sha(source)==expected
   ins.extend([{'path':str(source),'sha256':sha(source)},*artifacts(NATIVE,owner)])
  rec={'source_module':old,'destination_module':m,'attempt':attempt,'folder':str(folder.relative_to(ROOT)),'copy_kind':row.get('complete_original_parent_complement',{}).get('kind','whole_original_module'),'frozen_inputs':ins,'captures':{},'public_roots_filtered':0,'original_parent_rows_modified':False,'scoped_comparison_complete':False,'batch':str(batch.relative_to(ROOT)),'actual_callee_owner_profile':ownerprofiles.get(m),'original_owner_modules':[old,*extraowners],'actual_original_witness_spec':witnesses.get(m)}
  prev=state['modules'].get(m,{});candidate=prev.get('captures',{}).get('original-unfiltered');native_ins=[x for x in prev.get('frozen_inputs',[])if Path(x['path']).is_relative_to(NATIVE)]
  if candidate and prev.get('capture_exit')==0 and native_ins and prev.get('actual_callee_owner_profile')==ownerprofiles.get(m):
   assert all(Path(x['path']).exists()and sha(Path(x['path']))==x['sha256']for x in native_ins),('Original inputs changed',m)
   assert sha(ROOT/candidate['path'])==candidate['gzip_sha256'],('Original capture changed',m)
   rec['captures']['original-unfiltered']=dict(candidate)
   rec['reused_immutable_original_capture']={'previous_folder':prev['folder'],'original_capture_sha256':candidate['gzip_sha256'],'native_inputs':native_ins,'all_original_rows_retained_byte_for_byte':True,'previous_actual_private_name_pairs':str(Path(prev['folder'])/'actual-private-name-pairs.json')}
  else:
   originals.append(row)
   if candidate:rec['necessary_original_profile_recapture_reason']='Previously raw canonicalization used default physical module owner; corrected original/copy callee owner witness requires one narrow unchanged-V3 recapture. Both preceding raw captures retained.'
  recs[m]=rec
 oldtsv=batch/'original-modules.tsv';newtsv=batch/'public-modules.tsv'
 oldtsv.write_text(''.join(owner+'\t'+x['destination_module']+'\n'for x in originals for owner in[x['source_module'],*companions.get(x['destination_module'],{}).get('source_modules',[])]));newtsv.write_text(''.join(x['destination_module']+'\t'+x['destination_module']+'\n'for x in group))
 renames=A/'exact-module-renames.tsv'
 profiled=[r for r in group if ownerprofiles.get(r['destination_module'])]
 if profiled:
  assert len(group)==1,('Owner correction must be a narrow one-module invocation',group)
  profile=ownerprofiles[profiled[0]['destination_module']];renames=batch/'actual-callee-owner-renames.tsv'
  renames.write_text(''.join(x['original_module']+'\t'+x['actual_public_owner']+'\n'for x in profile['pairs'])+(A/'exact-module-renames.tsv').read_text())
 errors=[];threads=[];fifos=[]
 def consume(side,expected):
  fifo=batch/(side+'.fifo');os.mkfifo(fifo);fifos.append(fifo)
  def worker():
   streams={};stats={}
   try:
    for m in expected:
     path=folders[m]/(side+'.jsonl.gz');raw=path.open('wb');z=gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0);streams[m]=(path,raw,z);stats[m]={'h':hashlib.sha256(),'names':[],'bytes':0,'proofs':0}
    with fifo.open('rb')as inp:
     for line in inp:
      d=json.loads(line);m=d['module'];assert m in expected,('Unexpected actual module row',side,m)
      st=stats[m];assert d['name']not in st['names'],('Duplicate actual root',m,d['name']);st['names'].append(d['name']);st['h'].update(line);st['bytes']+=len(line);st['proofs']+=d['kind']=='theorem';streams[m][2].write(line)
    for m,(path,raw,z)in streams.items():
     z.close();raw.close();st=stats[m];recs[m]['captures'][side]={'path':str(path.relative_to(ROOT)),'gzip_sha256':sha(path),'uncompressed_sha256':st['h'].hexdigest(),'actual_roots':len(st['names']),'whole_theorem_proofs':st['proofs'],'uncompressed_bytes':st['bytes'],'actual_root_names':st['names']}
   except BaseException as e:errors.append([side,repr(e)])
  t=threading.Thread(target=worker,daemon=True);t.start();threads.append(t)
 consume('original-unfiltered',{x['destination_module']for x in originals});consume('public-unfiltered',{x['destination_module']for x in group})
 cmd=[PROBE,'lake','env','lean','--run',str(EXPORTER),str(oldtsv),str(newtsv),str(renames),str(fifos[0]),str(fifos[1]),str(batch/'actual-private-name-pairs.json')]
 start=time.monotonic()
 with(batch/'export.log').open('w')as log:result=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(NATIVE/'.lake/build/lib/lean')),stdout=log,stderr=subprocess.STDOUT)
 for fifo in fifos:
  try:fd=os.open(fifo,os.O_WRONLY|os.O_NONBLOCK);os.close(fd)
  except OSError:pass
 for t in threads:t.join()
 for f in fifos:f.unlink()
 elapsed=round(time.monotonic()-start,3)
 batch_record={'modules':[x['destination_module']for x in group],'unfiltered_original_parents_actually_exported':[owner for x in originals for owner in[x['source_module'],*companions.get(x['destination_module'],{}).get('source_modules',[])]],'original_parents_reused':[x['source_module']for x in group if x not in originals],'exit_code':result.returncode,'errors':errors,'seconds':elapsed,'command':cmd,'frozen_exporter_sha256':sha(EXPORTER),'frozen_comparator_sha256':sha(COMPARATOR),'public_roots_filtered':0,'rows_modified':False}
 (batch/'receipt.json').write_text(json.dumps(batch_record,indent=2)+'\n')
 for row in group:
  m=row['destination_module'];rec=recs[m]
  assert all(Path(x['path']).exists()and sha(Path(x['path']))==x['sha256']for x in rec['frozen_inputs']),('Input changed during capture',m)
  rec.update(capture_exit=result.returncode,capture_seconds=elapsed,transport_errors=errors,export_command=cmd)
  pair_dest=folders[m]/'actual-private-name-pairs.json';pair_dest.write_bytes((batch/'actual-private-name-pairs.json').read_bytes())
  state['modules'][m]=rec;save()
 for row in group:
  m=row['destination_module'];rec=recs[m]
  if result.returncode==0 and not errors:compare_one(rec,folders[m])
  state['modules'][m]=rec;save()
  print(json.dumps({'module':m,'batch':serial,'capture_exit':result.returncode,'comparison':rec.get('every_actual_new_root_comparison',{})}),flush=True)
 if result.returncode or errors:state['status']='BLOCKED_BATCH_ACTUAL_EXPORT';save();raise SystemExit(1)
while True:
 pending=[r for r in rows if not valid(r)];state['captured_and_compared_modules']=len(rows)-len(pending);save()
 if not pending:break
 # A pre-existing .olean/.hash is NOT evidence for a newly edited source.
 # During this warm build use only its explicit completed-target log; all
 # remaining cached artifacts become ready only after full build success.
 buildlog=args.build_log.read_text();built=set(re.findall(r'Built (Hironaka[\w.]*) \(',buildlog));fullpass='Build completed successfully' in buildlog
 ready=[r for r in pending if (fullpass or r['destination_module']in built)and Path(str(ROOT/'.lake/build/lib/lean'/(r['destination_module'].replace('.','/')+'.olean'))+'.hash').exists()]
 if not ready:
  live=subprocess.run(['ps','-p',str(args.build_pid),'-o','comm='],capture_output=True,text=True).stdout.strip()=='lake'
  if not live:state['status']='WAITING_MISSING_ACTUAL_PUBLIC_ARTIFACTS';save();raise SystemExit(3)
  time.sleep(3);continue
 first=ready[0]
 if ownerprofiles.get(first['destination_module']):group=[first]
 else:group=[r for r in ready if not ownerprofiles.get(r['destination_module'])][:8]
 capture_group(group)
state['captured_and_compared_modules']=len(rows);state['all_actual_public_roots']=sum(r['captures']['public-unfiltered']['actual_roots']for r in state['modules'].values());state['all_original_parent_roots_retained']=sum(r['captures']['original-unfiltered']['actual_roots']for r in state['modules'].values());state['status']='PASS_ALL_ACTUAL_NEW_ROOTS_FULL_STRUCTURAL_EXPR'if all(r['every_actual_new_root_comparison']['exit_code']==0 for r in state['modules'].values())else'BLOCKED_ACTUAL_NEW_ROOT_DIFFERENCES_RETAINED_TYPED_FRONTEND_ISOLATION_NOT_YET_ACCEPTED';save();print(state['status'],flush=True)
if not state['status'].startswith('PASS'):raise SystemExit(1)
