#!/usr/bin/env python3
"""Lossless whole-module expression capture using the UNCHANGED frozen V3 exporter.

FIFO transport only compresses complete untouched exporter rows, split by actual
module. Every moduleData constant (including private/generated/syntax helpers)
is retained. The unchanged full Expr DAG comparator checks one full module at
a time with no root filters, defeq, alpha conversion, waivers or allowed extras.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,subprocess,tempfile,threading,time
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
p=argparse.ArgumentParser();p.add_argument('--attempt',required=True);args=p.parse_args()
OUT=A/args.attempt;assert not OUT.exists(),'Preserve all earlier complete/rejected captures';OUT.mkdir()
records=json.loads((A/'provenance.json').read_text());expected={x['destination_module']for x in records};assert len(expected)==316
public_inventory=json.loads((A/'new-public-actual-name-inventory.json').read_text())
public_actual={x['module']:[r['actual_name']for r in x['actual_roots']]for x in public_inventory}
assert set(public_actual)==expected
empty_public={m for m,roots in public_actual.items()if not roots}
assert empty_public=={x['destination_module']for x in records if x.get('complete_original_parent_complement',{}).get('kind')=='pure_existing_support_imports'}
NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
EXPORTER=ROOT/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
V2=ROOT/'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean'
COMPARATOR=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
profiles=json.loads((A/'initial-port-plan.json').read_text())['toolchain_profiles']
for f in [EXPORTER,V2,COMPARATOR]:assert sha(f)==profiles[str(f.relative_to(ROOT))],('Frozen tool changed',f)
for row in records:
 assert sha(ROOT/row['destination_path'])==row['destination_sha256'],row['destination_module']
 assert sha(NATIVE/(row['source_module'].replace('.','/')+'.lean'))==row['source_sha256'],row['source_module']
 for base,m in [(ROOT,row['destination_module']),(NATIVE,row['source_module'])]:assert(base/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')).is_file(),('Missing exact original/copy artifact',m)
state={'status':'CAPTURING','whole_modules':316,'accepted_checkpoint':'82934a028fb2c94d5a706bf66343fd4614e8a884','published_source_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','frozen_profiles':{str(f.relative_to(ROOT)):sha(f)for f in [EXPORTER,V2,COMPARATOR]},'captures':{},'root_filters':0,'auxiliary_skips':0,'allowed_extras':0,'defeq_or_alpha_comparison':False,'proof_or_instance_context_edits':0}
(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
errors=[];threads=[];fifos=[]

def consume(side,fifo):
 folder=OUT/side;folder.mkdir();files={};global_hash=hashlib.sha256();total=0;order=[];active=None;stream=None;rawout=None;record=None
 try:
  with fifo.open('rb')as src:
   for line in src:
    row=json.loads(line);m=row['module'];assert m in expected,('Unexpected module',m)
    if m!=active:
     if stream is not None:
      stream.close();rawout.close();record['gzip_sha256']=sha(folder/(active+'.jsonl.gz'));record['gzip_bytes']=(folder/(active+'.jsonl.gz')).stat().st_size
     assert m not in files,('Noncontiguous repeated module',m)
     active=m;order.append(m);dest=folder/(m+'.jsonl.gz');rawout=dest.open('wb');stream=gzip.GzipFile(filename='',mode='wb',fileobj=rawout,mtime=0)
     record={'path':str(dest.relative_to(ROOT)),'actual_roots':0,'uncompressed_bytes':0,'uncompressed_sha256_object':hashlib.sha256(),'root_names':[]};files[m]=record
    assert row['name']not in record['root_names'],('Duplicate actual root',m,row['name'])
    record['root_names'].append(row['name']);record['actual_roots']+=1;record['uncompressed_bytes']+=len(line);record['uncompressed_sha256_object'].update(line);global_hash.update(line);total+=1;stream.write(line)
  if stream is not None:
   stream.close();rawout.close();record['gzip_sha256']=sha(folder/(active+'.jsonl.gz'));record['gzip_bytes']=(folder/(active+'.jsonl.gz')).stat().st_size;stream=None;rawout=None
  missing=expected-set(files)
  assert not missing or(side=='standalone'and missing==empty_public),('Missing complete modules',side,sorted(missing))
  for m in missing:
   dest=folder/(m+'.jsonl.gz')
   with dest.open('wb')as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0):pass
   files[m]={'path':str(dest.relative_to(ROOT)),'actual_roots':0,'uncompressed_bytes':0,'uncompressed_sha256_object':hashlib.sha256(),'root_names':[],'gzip_sha256':sha(dest),'gzip_bytes':dest.stat().st_size,'zero_own_constants_verified_in_actual_moduleData':True}
  for r in files.values():r['uncompressed_sha256']=r.pop('uncompressed_sha256_object').hexdigest()
  if side=='standalone':
   for m,r in files.items():assert set(r['root_names'])==set(public_actual[m]),('Public actual moduleData root lost',m)
  state['captures'][side]={'modules':files,'module_order':order,'all_actual_roots':total,'complete_uncompressed_stream_sha256':global_hash.hexdigest()}
 except BaseException as e:errors.append((side,repr(e)))
 finally:
  if stream is not None:stream.close()
  if rawout is not None:rawout.close()

for side in ['native','standalone']:
 fifo=OUT/(side+'.fifo');os.mkfifo(fifo);fifos.append(fifo);t=threading.Thread(target=consume,args=(side,fifo),daemon=True);t.start();threads.append(t)
cmd=['/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh','lake','env','lean','--run',str(EXPORTER),str(A/'core-old-modules.tsv'),str(A/'core-new-modules.tsv'),str(A/'exact-module-renames.tsv'),str(fifos[0]),str(fifos[1]),str(OUT/'actual-private-name-pairs.json')]
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(NATIVE/'.lake/build/lib/lean'))
state['export_command']=cmd;start=time.monotonic()
with(OUT/'export.log').open('w')as f:proc=subprocess.run(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
for fifo in fifos:
 try:fd=os.open(fifo,os.O_WRONLY|os.O_NONBLOCK);os.close(fd)
 except OSError:pass
for t in threads:t.join()
for f in fifos:f.unlink()
state['export_exit']=proc.returncode;state['export_seconds']=round(time.monotonic()-start,3);state['transport_errors']=errors
(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
if proc.returncode or errors:state['status']='REJECTED_EXPORT_OR_CAPTURE';(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n');raise SystemExit(proc.returncode or 1)
reports={};compare_folder=OUT/'comparisons';compare_folder.mkdir()
for index,m in enumerate(sorted(expected),1):
 pair=[]
 with tempfile.TemporaryDirectory(prefix='hironaka-whole-module-expr-')as temp:
  temp=Path(temp)
  for side in ['native','standalone']:
   r=state['captures'][side]['modules'][m];dest=temp/(side+'.jsonl');h=hashlib.sha256();size=0;rows=0
   with gzip.open(ROOT/r['path'],'rb')as src,dest.open('wb')as out:
    for line in src:h.update(line);size+=len(line);rows+=1;out.write(line)
   assert h.hexdigest()==r['uncompressed_sha256']and size==r['uncompressed_bytes']and rows==r['actual_roots']
   pair.append(dest)
  report=compare_folder/(m+'.json');cmd=['python3',str(COMPARATOR),str(pair[0]),str(pair[1]),str(report)]
  with(compare_folder/(m+'.log')).open('w')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
  result=json.loads(report.read_text());reports[m]={'exit_code':p.returncode,'status':result['status'],'path':str(report.relative_to(ROOT)),'sha256':sha(report),'all_actual_constants':result['old']['all_actual_constants'],'standalone_actual_constants':result['native']['all_actual_constants'],'whole_theorem_proofs':sum(c['theorem_proofs_exact']for c in result['module_counts'].values())}
  if p.returncode:
   state['status']='BLOCKED_EXACT_DIFFERENCE';state['comparisons']=reports;(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n');print('EXACT_DIFFERENCE_RETAINED '+m,flush=True)
 print(f'COMPLETE_RAW_MODULE_COMPARISON {index}/316 {m} exit={p.returncode}',flush=True)
state['comparisons']=reports;state['status']='PASS_ALL316_RAW_PARENT_TYPES_WHOLE_VALUES_AND_PROOFS'if all(x['exit_code']==0 for x in reports.values())else'BLOCKED_COMPLETE_ALL316_RAW_PARENT_COMPARISONS_RETAINED';state['all_original_parent_roots_retained']=sum(x['all_actual_constants']for x in reports.values());state['raw_comparator_exact_theorem_proofs']=sum(x['whole_theorem_proofs']for x in reports.values());state['raw_parent_vs_actual_copy_scope']='Entire original parents retained, including preceding original support roots reused by seven complements and two pure import adapters; raw differences are never silently waived';(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n');print(json.dumps({k:v for k,v in state.items()if k not in ['captures','comparisons']}),flush=True)
if any(x['exit_code']for x in reports.values()):raise SystemExit(1)
