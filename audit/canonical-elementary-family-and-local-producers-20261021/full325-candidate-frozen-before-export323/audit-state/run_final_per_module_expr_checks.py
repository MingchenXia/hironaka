#!/usr/bin/env python3
"""FINAL per-ready-module lossless V3 capture and unchanged structural checks.

Every original parent is captured unfiltered. For complete original complements,
select ORIGINAL rows verbatim for EVERY actual public moduleData root. Pure
import adapters are explicitly zero-root files. No public root is filtered;
notation discrepancies remain blocked pending independent typed isolation.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,subprocess,threading,time
A=Path(__file__).resolve().parent;ROOT=A.parents[1];NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
p=argparse.ArgumentParser();p.add_argument('--build-pid',type=int,required=True);args=p.parse_args()
PROBE='/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh'
EXPORTER=ROOT/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
V2=ROOT/'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean'
COMPARATOR=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
profiles=json.loads((A/'initial-port-plan.json').read_text())['toolchain_profiles']
for f in [EXPORTER,V2,COMPARATOR]:assert sha(f)==profiles[str(f.relative_to(ROOT))],('Frozen tool changed',f)
modules=json.loads((A/'provenance.json').read_text());assert len(modules)==316
OUT=A/'final-per-module-expressions';OUT.mkdir(exist_ok=True);statefile=OUT/'status.json'
state=json.loads(statefile.read_text())if statefile.exists()else {'status':'RUNNING_FINAL_PER_MODULE_CAPTURES','modules':{},'accepted_checkpoint':'82934a028fb2c94d5a706bf66343fd4614e8a884','published_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','frozen_profiles':{str(f.relative_to(ROOT)):sha(f)for f in [EXPORTER,V2,COMPARATOR]},'public_roots_filtered':0,'proof_type_token_edits':0,'defeq_or_alpha_comparison':False,'raw_frontend_differences_waived':False}

def save():statefile.write_text(json.dumps(state,indent=2)+'\n')
def artifacts(base,m):
 p=base/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 return [{'path':str(q),'sha256':sha(q),'bytes':q.stat().st_size}for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server')]if q.exists()]
def valid(record):
 return record.get('capture_exit')==0 and all(Path(x['path']).exists()and sha(Path(x['path']))==x['sha256']for x in record.get('frozen_inputs',[]))and record.get('scoped_comparison_complete')is True

def capture(row):
 m=row['destination_module'];old=row['source_module'];folder=OUT/m;attempt=1
 while(folder/('attempt'+str(attempt))).exists():attempt+=1
 folder=folder/('attempt'+str(attempt));folder.mkdir(parents=True)
 native_source=NATIVE/(old.replace('.','/')+'.lean');public_source=ROOT/row['destination_path']
 assert sha(native_source)==row['source_sha256']and sha(public_source)==row['destination_sha256'],('Source drift',m)
 inputs=[{'path':str(native_source),'sha256':sha(native_source)},{'path':str(public_source),'sha256':sha(public_source)},*artifacts(NATIVE,old),*artifacts(ROOT,m)]
 assert artifacts(NATIVE,old)and artifacts(ROOT,m),('Missing actual main kernel artifact',m)
 # Official Lake currently writes monolithic .olean for these modules; preserve
 # every actual optional split private/server part when present, never invent it.
 oldtsv=folder/'original-module.tsv';newtsv=folder/'public-module.tsv';oldtsv.write_text(old+'\t'+m+'\n');newtsv.write_text(m+'\t'+m+'\n')
 rec={'source_module':old,'destination_module':m,'attempt':attempt,'folder':str(folder.relative_to(ROOT)),'copy_kind':row.get('complete_original_parent_complement',{}).get('kind','whole_original_module'),'frozen_inputs':inputs,'captures':{},'public_roots_filtered':0,'original_parent_rows_modified':False,'scoped_comparison_complete':False};errors=[];fifos=[];threads=[]
 # A single NEW-source authentic original elaboration-context restoration may
 # invalidate its public artifact. Reuse the preceding immutable ORIGINAL
 # whole-parent capture; export only the current public module with the SAME
 # unchanged frozen V3. Never repeat or modify the original serialization.
 reuse_original = None
 if m == 'Hironaka.Resolution.HironakaSmoothCentreRealDomainNearbyFreeness':
  previous = state['modules'].get(m,{})
  native_inputs = [x for x in previous.get('frozen_inputs',[]) if Path(x['path']).is_relative_to(NATIVE)]
  candidate = previous.get('captures',{}).get('original-unfiltered')
  if previous.get('capture_exit') == 0 and native_inputs and candidate:
   assert all(Path(x['path']).exists() and sha(Path(x['path'])) == x['sha256'] for x in native_inputs),('Original capture inputs changed',m)
   assert candidate['gzip_sha256'] == sha(ROOT/candidate['path']),('Original capture changed',m)
   previous_pairs = ROOT/previous['folder']/'actual-private-name-pairs.json'
   assert json.loads(previous_pairs.read_text()) == [],('Unexpected private-owner mapping in original capture',m)
   reuse_original = dict(candidate)
   rec['captures']['original-unfiltered'] = reuse_original
   rec['reused_immutable_original_capture'] = {'previous_folder':previous['folder'],'original_capture_sha256':candidate['gzip_sha256'],'native_inputs':native_inputs,'all_original_rows_retained_byte_for_byte':True,'private_owner_pairs':[]}
 def consume(side,fifo):
  dest=folder/(side+'.jsonl.gz');h=hashlib.sha256();count=0;size=0;names=[];theorems=0
  try:
   with fifo.open('rb')as src,dest.open('wb')as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0)as zipped:
     for line in src:
      r=json.loads(line);assert r['module']==m,(m,r['module']);assert r['name']not in names,('Duplicate actual row',m,r['name'])
      names.append(r['name']);count+=1;size+=len(line);theorems+=r['kind']=='theorem';h.update(line);zipped.write(line)
   rec['captures'][side]={'path':str(dest.relative_to(ROOT)),'gzip_sha256':sha(dest),'uncompressed_sha256':h.hexdigest(),'actual_roots':count,'whole_theorem_proofs':theorems,'uncompressed_bytes':size,'actual_root_names':names}
  except BaseException as e:errors.append([side,repr(e)])
 for side in (['original-empty-recapture-sink','public-unfiltered'] if reuse_original else ['original-unfiltered','public-unfiltered']):
  fifo=folder/(side+'.fifo');os.mkfifo(fifo);fifos.append(fifo);t=threading.Thread(target=consume,args=(side,fifo),daemon=True);t.start();threads.append(t)
 if reuse_original:
  oldtsv=folder/'empty-original-roster.tsv';oldtsv.write_text('')
 cmd=[PROBE,'lake','env','lean','--run',str(EXPORTER),str(oldtsv),str(newtsv),str(A/'exact-module-renames.tsv'),str(fifos[0]),str(fifos[1]),str(folder/'actual-private-name-pairs.json')]
 start=time.monotonic()
 with(folder/'export.log').open('w')as log:proc=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(NATIVE/'.lake/build/lib/lean')),stdout=log,stderr=subprocess.STDOUT)
 for fifo in fifos:
  try:fd=os.open(fifo,os.O_WRONLY|os.O_NONBLOCK);os.close(fd)
  except OSError:pass
 for t in threads:t.join()
 for f in fifos:f.unlink()
 rec.update(capture_exit=proc.returncode,capture_seconds=round(time.monotonic()-start,3),transport_errors=errors,export_command=cmd)
 assert all(sha(Path(x['path']))==x['sha256']for x in inputs),('Actual source/artifact changed during capture',m)
 if proc.returncode or errors:return rec
 if reuse_original:
  assert rec['captures']['original-empty-recapture-sink']['actual_roots'] == 0,('Original roster was not empty',m)
 oldplain=folder/'original-unfiltered.jsonl';newplain=folder/'public-unfiltered.jsonl'
 for side,dest in [('original-unfiltered',oldplain),('public-unfiltered',newplain)]:
  with gzip.open(ROOT/rec['captures'][side]['path'],'rb')as source,dest.open('wb')as out:
   for line in source:out.write(line)
  assert sha(dest)==rec['captures'][side]['uncompressed_sha256']
 def compare(orig,name):
  report=folder/(name+'.json');command=['python3',str(COMPARATOR),str(orig),str(newplain),str(report)]
  with(folder/(name+'.log')).open('w')as log:result=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
  r=json.loads(report.read_text());return {'exit_code':result.returncode,'report':str(report.relative_to(ROOT)),'report_sha256':sha(report),'status':r['status'],'actual_public_roots':r['native']['all_actual_constants'],'original_roots_compared':r['old']['all_actual_constants'],'entire_theorem_proofs_exact':sum(v['theorem_proofs_exact']for v in r['module_counts'].values()),'missing':r['missing'],'extra':r['native_extras'],'difference_roots':sorted({x['constant'][1]for x in r['differences']})}
 rec['raw_complete_parent_comparison']=compare(oldplain,'raw-complete-parent-comparison')
 if rec['copy_kind']=='whole_original_module':rec['every_actual_new_root_comparison']=rec['raw_complete_parent_comparison']
 else:
  public_names=set(rec['captures']['public-unfiltered']['actual_root_names']);selected=folder/'original-selected-verbatim-for-all-public-roots.jsonl';found=set();discarded=[]
  with oldplain.open('rb')as source,selected.open('wb')as out:
   for line in source:
    r=json.loads(line)
    if r['name']in public_names:out.write(line);found.add(r['name'])
    else:discarded.append(r['name'])
  assert found==public_names,('Actual public complement root has no original counterpart',m,public_names-found)
  if rec['copy_kind']=='pure_existing_support_imports':assert not public_names,('Import adapter has undeclared own roots',m)
  rec['original_parent_selection']={'source_capture':rec['captures']['original-unfiltered']['path'],'selected_original_rows_sha256':sha(selected),'all_actual_public_roots_retained':True,'selected_rows_modified':False,'original_parent_roots_already_reused_from_preceding_support':discarded,'original_parent_roots_unfiltered_in_raw_capture':True}
  rec['every_actual_new_root_comparison']=compare(selected,'all-actual-new-complement-root-comparison');selected.unlink()
 rec['scoped_comparison_complete']=True
 oldplain.unlink();newplain.unlink()
 return rec

while True:
 pending=[x for x in modules if not valid(state['modules'].get(x['destination_module'],{}))];state['captured_and_compared_modules']=len(modules)-len(pending);save()
 if not pending:break
 ready=[x for x in pending if(Path(str(ROOT/'.lake/build/lib/lean'/(x['destination_module'].replace('.','/')+'.olean'))+'.hash')).exists()]
 if not ready:
  live=subprocess.run(['ps','-p',str(args.build_pid),'-o','comm='],capture_output=True,text=True).stdout.strip()=='lake'
  if not live:state['status']='WAITING_MISSING_ACTUAL_PUBLIC_ARTIFACTS';save();raise SystemExit(3)
  time.sleep(3);continue
 for row in ready:
  rec=capture(row);state['modules'][row['destination_module']]=rec;save()
  if rec['capture_exit']or rec['transport_errors']:state['status']='BLOCKED_ACTUAL_EXPORT';save();raise SystemExit(1)
  r=rec['every_actual_new_root_comparison'];print(json.dumps({'module':row['destination_module'],'capture_exit':rec['capture_exit'],'actual_public_roots':r['actual_public_roots'],'scoped_structural_comparison_exit':r['exit_code'],'exact_proofs':r['entire_theorem_proofs_exact'],'difference_roots':r['difference_roots']}),flush=True)
state['captured_and_compared_modules']=len(modules);state['all_actual_public_roots']=sum(x['captures']['public-unfiltered']['actual_roots']for x in state['modules'].values());state['all_original_parent_roots_retained']=sum(x['captures']['original-unfiltered']['actual_roots']for x in state['modules'].values());state['status']='PASS_ALL_ACTUAL_NEW_ROOTS_FULL_STRUCTURAL_EXPR'if all(x['every_actual_new_root_comparison']['exit_code']==0 for x in state['modules'].values())else'BLOCKED_ACTUAL_NEW_ROOT_DIFFERENCES_RETAINED_TYPED_FRONTEND_ISOLATION_NOT_YET_ACCEPTED';save();print(state['status'],flush=True)
if not state['status'].startswith('PASS'):raise SystemExit(1)
