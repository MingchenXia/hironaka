"""Independent candidate06 replay with every production write forbidden."""
from pathlib import Path
import contextlib, hashlib, io, json, runpy, sys
A=Path(__file__).resolve().parents[2]
R=A.parents[1]
O=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (O/'final-read-only-no-op.json').exists(), 'Once-only witness already exists'
previous=json.loads((O.parent/'attempt05/final-read-only-no-op-input-fingerprints.json').read_text())
partition=json.loads((A/'deferred-complete-module-partition.json').read_text())
removed={r['destination_path']for r in partition['deferred_complete_modules']+partition['deferred_complete_blueprint_chapters']}
assert len(removed)==4
assert all(not (R/p).exists()for p in removed)
paths={p for p in previous if p not in removed}
new_inputs=['deferred-complete-module-partition.json','deferred-source-provenance.json','deferred-blueprint-provenance.json','standalone-import-scope-publication323.json','blueprint-external-index-two-module-partition-static.json','full325-candidate-frozen-before-export323/immutable-snapshot-manifest.json']
for name in new_inputs:
 p=A/name
 assert p.is_file(),p
 paths.add(str(p.relative_to(R)))
for row in partition['deferred_complete_modules']+partition['deferred_complete_blueprint_chapters']:
 p=A/row['canonical_draft_capture'];assert sha(p.read_bytes())==row['sha256']
 paths.add(str(p.relative_to(R)))
for key in ['full_candidate_umbrella','full_candidate_master']:
 p=A/partition[key]['capture'];assert sha(p.read_bytes())==partition[key]['sha256']
 paths.add(str(p.relative_to(R)))
for folder in ['attempt06-integration-before','blueprint-external-index-before-two-module-partition']:
 for p in (A/folder).rglob('*'):
  if p.is_file():paths.add(str(p.relative_to(R)))
for p in A.glob('*.py'):paths.add(str(p.relative_to(R)))
before={p:sha((R/p).read_bytes())for p in sorted(paths)}
receipt=A/'source-replay-receipt.json'
assert json.loads(receipt.read_text())['new_source_files']==323
old_write_text,old_write_bytes,old_unlink=Path.write_text,Path.write_bytes,Path.unlink
writes=[]
def blocked_text(path,data,*args,**kwargs):
 assert path.resolve()==receipt.resolve(),('Unexpected write',str(path))
 encoding=kwargs.get('encoding',args[0]if args else 'utf-8')or 'utf-8'
 raw=data.encode(encoding)
 assert path.read_bytes()==raw,('Receipt write is not a no-op',str(path))
 writes.append(str(path.relative_to(R)))
 return len(data)
def blocked_bytes(path,data,*args,**kwargs):raise AssertionError(('Forbidden write_bytes',str(path)))
def blocked_unlink(path,*args,**kwargs):raise AssertionError(('Forbidden unlink',str(path)))
stdout,stderr=io.StringIO(),io.StringIO()
sys.dont_write_bytecode=True
sys.path.insert(0,str(A))
sys.argv=[str(A/'sync_frozen_sources.py'),'--source-root','/workspace/archon-publish','--revision','4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','--check']
error=None
try:
 Path.write_text,Path.write_bytes,Path.unlink=blocked_text,blocked_bytes,blocked_unlink
 with contextlib.redirect_stdout(stdout),contextlib.redirect_stderr(stderr):runpy.run_path(str(A/'sync_frozen_sources.py'),run_name='__main__')
except BaseException as exc:
 error=repr(exc)
finally:
 Path.write_text,Path.write_bytes,Path.unlink=old_write_text,old_write_bytes,old_unlink
log=stdout.getvalue()+stderr.getvalue()
(O/'final-read-only-no-op.log').write_text(log)
(O/'final-read-only-no-op.exit').write_text('1\n'if error else'0\n')
assert error is None,error
assert writes==[str(receipt.relative_to(R))],writes
after={p:sha((R/p).read_bytes())for p in before}
assert before==after,'Tracked source/replay input changed during no-op'
fp=O/'final-read-only-no-op-input-fingerprints.json';fp.write_text(json.dumps(before,indent=2)+'\n')
d={'status':'PASS_ATTEMPT06_READ_ONLY_EXACT_323_SOURCE_BLUEPRINT_REPLAY_NO_OP','candidate':6,'fixed_ordinary_source_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','unconditional_receipt_write_intercepted_as_existing_byte_equality':writes,'production_and_replay_input_files_before_after_byte_identical':len(before),'whole_deferred_source_and_BP_paths_absent':sorted(removed),'no_runtime_Lean_kernel_or_Expr_invocation':True,'summary':json.loads(receipt.read_text()),'input_fingerprints_sha256':sha(fp.read_bytes()),'log_sha256':sha(log.encode()),'exit_code':0}
f=O/'final-read-only-no-op.json';f.write_text(json.dumps(d,indent=2)+'\n')
print(f)
print(sha(f.read_bytes()))
print('tracked_inputs',len(before))
