#!/usr/bin/env python3
"""Recapture one invalidated public artifact; reuse exact untouched original raw."""
from pathlib import Path
import argparse,gzip,hashlib,json,os,subprocess,sys,tempfile,time
A=Path(__file__).resolve().parent;D=A.parents[1]
p=argparse.ArgumentParser();p.add_argument('--module',required=True);p.add_argument('--original',type=Path,required=True);p.add_argument('--attempt',required=True);a=p.parse_args()
out=A/a.attempt;out.mkdir(exist_ok=False);plan=json.loads((A/'plan.json').read_text())
row=next(x for x in plan['source_modules']if x['destination_module']==a.module)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(D/row['destination_path']):sha(D/row['destination_path']),
 str(D/'.lake/build/lib/lean'/(a.module.replace('.','/')+'.olean')):sha(D/'.lake/build/lib/lean'/(a.module.replace('.','/')+'.olean')),
 str(a.original.resolve()):sha(a.original)}
(out/'empty-original-modules.tsv').write_text('');(out/'public-modules.tsv').write_text(a.module+'\t'+a.module+'\n')
mapping=A/'full-expressions-attempt01/exact-module-renames.tsv'
V3=A/'frozen-tools/CanonicalStandaloneAllScopedOwnersV3.lean';CMP=A/'frozen-tools/compare_full_expr_dag.py'
cmd=['/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh','flock','-s',
 '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock','lake','env','lean','--run',str(V3),
 str(out/'empty-original-modules.tsv'),str(out/'public-modules.tsv'),str(mapping),
 str(out/'empty-original.jsonl'),str(out/'public-unfiltered.jsonl'),str(out/'empty-private-pairs.json')]
start=time.monotonic()
with(out/'export.log').open('w')as log:r=subprocess.run(cmd,cwd=D,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT)
(out/'export.exit').write_text(str(r.returncode)+'\n');assert r.returncode==0
public=out/'public-unfiltered.jsonl';compressed=out/'public-unfiltered.jsonl.gz'
with public.open('rb')as src,compressed.open('wb')as raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0)as dst:
 for block in iter(lambda:src.read(1024*1024),b''):dst.write(block)
with tempfile.TemporaryDirectory(prefix='disjoint-original-reuse-')as td:
 original=Path(td)/'original.jsonl'
 with gzip.open(a.original,'rb')as src,original.open('wb')as dst:
  for block in iter(lambda:src.read(1024*1024),b''):dst.write(block)
 report=out/'comparison.json'
 with(out/'compare.log').open('w')as log:c=subprocess.run([sys.executable,str(CMP),str(original),str(public),str(report)],cwd=D,stdout=log,stderr=subprocess.STDOUT)
public_hash=sha(public);public.unlink()
assert inputs=={path:sha(Path(path))for path in inputs}
receipt={'status':'PASS_REUSED_ORIGINAL_FULL_EXPR'if c.returncode==0 else'BLOCKED_EXACT_DIFFERENCE_RETAINED',
 'module':a.module,'export_exit':r.returncode,'compare_exit':c.returncode,
 'original_raw_reused_verbatim':str(a.original),'original_raw_sha256':sha(a.original),
 'new_public_raw_gzip_sha256':sha(compressed),'new_public_raw_sha256':public_hash,
 'frozen_serializer_sha256':sha(V3),'frozen_comparator_sha256':sha(CMP),
 'source_artifact_inputs':inputs,'all_inputs_unchanged':True,'all_children_reaped':True,
 'public_root_filters':0,'numeric_or_proof_name_rewrites':False,'seconds':round(time.monotonic()-start,3)}
(out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));raise SystemExit(c.returncode)
