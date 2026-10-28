#!/usr/bin/env python3
"""New paired scopes only; unchanged frozen V3 serializer and DAG comparator."""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,json,os,subprocess,sys,tempfile,threading,time
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent;D=A.parents[1]
p=argparse.ArgumentParser();p.add_argument('--attempt',required=True)
p.add_argument('--only',action='append',default=[])
p.add_argument('--actual-owner-inputs',type=Path)
p.add_argument('--scope',choices=['whole','support'],default='whole')
args=p.parse_args()
plan=json.loads((A/'installation-plan.json').read_text());rows=plan['source_modules'];N=Path(plan['native_source_checkout'])/'TranscendentalNakamaye'
F=A.parent/'disjoint-producers-20261028'/'frozen-tools'
plan['frozen_tools']=json.loads((A.parent/'disjoint-producers-20261028'/'plan.json').read_text())['frozen_tools']
if args.scope=='support': rows=plan['support_extracts']
if args.only:
 assert set(args.only)<={r['destination_module']for r in rows}
 rows=[r for r in rows if r['destination_module']in args.only]
owner_inputs=json.loads(args.actual_owner_inputs.read_text())if args.actual_owner_inputs else{}
owner_pairs=owner_inputs.get('per_capture_owner_pairs',{})
if args.scope=='support':
 assert not owner_pairs
 owner_pairs={r['destination_module']:[[r['source_module'],r['destination_module']]]for r in rows}
OUT=A/args.attempt;OUT.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
V3=F/('BoundedSelectedSupportV3.lean'if args.scope=='support'else'CanonicalStandaloneAllScopedOwnersV3.lean');CMP=F/'compare_full_expr_dag.py'
tool_path=('audit/phase5-original-producers-20261021/support-full-expressions/BoundedSelectedSupportV3.lean'
 if args.scope=='support'else'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean')
for original,tool in [(tool_path,V3),
 ('audit/local-sharp-curves-20261015/compare_full_expr_dag.py',CMP)]:
 assert sha(tool)==plan['frozen_tools'][original]['sha256']
spec=importlib.util.spec_from_file_location('frozen_map',D/'scripts/upstream_namespace_map.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
paths=subprocess.check_output(['git','-C',str(plan['native_source_checkout']),'ls-tree','-r','--name-only',plan['native_revision'],'--','TranscendentalNakamaye/TranscendentalNakamaye'],text=True).splitlines()
modules=[x.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.')for x in paths if x.endswith('.lean')]
mapping=''.join(m+'\t'+names.new_mod(m)+'\n'for m in modules if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.')))
(OUT/'exact-module-renames.tsv').write_text(mapping)
inputs={}
for r in rows:
 for b,m in [(N,r['source_module']),(D,r['destination_module'])]:
  for path in [b/(m.replace('.','/')+'.lean'),b/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')]:inputs[str(path)]=sha(path)
(OUT/'before-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
state={'status':'RUNNING','whole_modules':len(rows),'native_revision':plan['native_revision'],
 'frozen_serializer_sha256':sha(V3),'frozen_comparator_sha256':sha(CMP),'batches':[],'comparisons':{},
 'public_root_filters':0,'allowed_extras':0,'defeq_or_alpha_or_numeric_erasure':False,
 'actual_owner_input_profiles':owner_pairs,
 'new_comparison_scope_reason':('ALL new support physical roots with unique original CI witnesses'if args.scope=='support'
 else'Actual physical-callee ownership correction only'if owner_pairs else'Initial whole-module comparison'),
 'comparison_scope':args.scope}
def save(): (OUT/'verification.json').write_text(json.dumps(state,indent=2)+'\n')
save();env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(N/'.lake/build/lib/lean'))
batchsize=1 if owner_pairs else 7
for offset in range(0,len(rows),batchsize):
 batch=rows[offset:offset+batchsize];B=OUT/f'batch-{offset//batchsize+1:02d}';B.mkdir()
 expected={r['destination_module']for r in batch}; captures={};errors=[];threads=[];fifos=[]
 (B/'original-modules.tsv').write_text(''.join(r['source_module']+'\t'+r['destination_module']+'\n'for r in batch))
 (B/'public-modules.tsv').write_text(''.join(r['destination_module']+'\t'+r['destination_module']+'\n'for r in batch))
 profile=''.join(a+'\t'+b+'\n'for r in batch for a,b in owner_pairs.get(r['destination_module'],[]))
 (B/'actual-module-owner-inputs.tsv').write_text(profile+mapping)
 def consume(side,fifo):
  folder=B/side;folder.mkdir();active=None;gz=None;raw=None;records={}
  try:
   with fifo.open('rb')as stream:
    for line in stream:
     obj=json.loads(line);m=obj['module'];assert m in expected,(side,m)
     if m!=active:
      if gz is not None:gz.close();raw.close()
      assert m not in records,('Non-contiguous module',m)
      active=m;raw=(folder/(m+'.jsonl.gz')).open('wb');gz=gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0)
      records[m]={'actual_roots':0,'names':[],'uncompressed_bytes':0,'digest':hashlib.sha256()}
     rec=records[m];assert obj['name']not in rec['names'],('Duplicate physical root',m,obj['name'])
     rec['names'].append(obj['name']);rec['actual_roots']+=1;rec['uncompressed_bytes']+=len(line);rec['digest'].update(line);gz.write(line)
   if gz is not None:gz.close();raw.close();gz=None;raw=None
   assert set(records)==expected,('Missing complete module',side,expected-set(records))
   for m,rec in records.items():
    rec['uncompressed_sha256']=rec.pop('digest').hexdigest();rec['gzip_sha256']=sha(folder/(m+'.jsonl.gz'))
   captures[side]=records
  except BaseException as e:errors.append([side,repr(e)])
  finally:
   if gz is not None:gz.close()
   if raw is not None:raw.close()
 for side in ['original','public']:
  fifo=B/(side+'.fifo');os.mkfifo(fifo);fifos.append(fifo);thread=threading.Thread(target=consume,args=(side,fifo));thread.start();threads.append(thread)
 cmd=['/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh','flock','-s',
  '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock','lake','env','lean','--run',str(V3),
  str(B/'original-modules.tsv'),str(B/'public-modules.tsv'),str(B/'actual-module-owner-inputs.tsv'),
  str(fifos[0]),str(fifos[1]),str(B/'actual-private-pairs.json')]
 start=time.monotonic()
 with(B/'export.log').open('w')as log:proc=subprocess.run(cmd,cwd=D,env=env,stdout=log,stderr=subprocess.STDOUT)
 for fifo in fifos:
  try:fd=os.open(fifo,os.O_WRONLY|os.O_NONBLOCK);os.close(fd)
  except OSError:pass
 for thread in threads:thread.join()
 for fifo in fifos:fifo.unlink()
 result={'exit':proc.returncode,'seconds':round(time.monotonic()-start,3),'command':cmd,
  'errors':errors,'all_children_and_capture_threads_reaped':True,'captures':captures}
 (B/'capture-verification.json').write_text(json.dumps(result,indent=2)+'\n');state['batches'].append(result);save()
 assert proc.returncode==0 and not errors,('Retained failed full export',B)
 for m in sorted(expected):
  dest=B/'comparisons';dest.mkdir(exist_ok=True)
  with tempfile.TemporaryDirectory(prefix='disjoint-full-expr-')as td:
   pair=[]
   for side in ['original','public']:
    raw=Path(td)/(side+'.jsonl');h=hashlib.sha256()
    with gzip.open(B/side/(m+'.jsonl.gz'),'rb')as src,raw.open('wb')as out:
     for line in src:h.update(line);out.write(line)
    assert h.hexdigest()==captures[side][m]['uncompressed_sha256'];pair.append(raw)
   report=dest/(m+'.json')
   with(dest/(m+'.log')).open('w')as log:p=subprocess.run([sys.executable,str(CMP),str(pair[0]),str(pair[1]),str(report)],cwd=D,stdout=log,stderr=subprocess.STDOUT)
   payload=json.loads(report.read_text());state['comparisons'][m]={'exit':p.returncode,'status':payload['status'],
    'report':str(report.relative_to(A)),'sha256':sha(report),'original_actual_roots':captures['original'][m]['actual_roots'],
    'public_actual_roots':captures['public'][m]['actual_roots']}
   print(f'WHOLE_NEW_EXPR {m} exit={p.returncode}',flush=True);save()
assert inputs=={path:sha(Path(path))for path in inputs},'Source/artifact changed during paired captures'
state['source_artifact_inputs_unchanged']=True
state['status']=f'PASS_ALL{len(rows)}_WHOLE_TYPES_VALUES_PROOFS'if all(r['exit']==0 for r in state['comparisons'].values())else'BLOCKED_EXACT_DIFFERENCE_RETAINED'
save();print(state['status'],flush=True)
raise SystemExit(0 if state['status'].startswith('PASS')else 1)
