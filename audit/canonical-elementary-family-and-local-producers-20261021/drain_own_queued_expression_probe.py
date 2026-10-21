from pathlib import Path
import os,time,fcntl,signal,json,datetime,subprocess
A=Path(__file__).resolve().parent;runtime=Path('/workspace/archon-nakamaye/work/lean-runtime');driver=259879
cmd=Path(f'/proc/{driver}/cmdline').read_bytes().split(b'\0');assert any(b'run_final_per_module_expr_checks.py'in x for x in cmd)
files=[(runtime/f'probe-{k}.lock').open('a')for k in [1,2]]
receipt={'status':'WAITING_FOR_ACTIVE_READERS_TO_FINISH','driver_pid':driver,'active_compiler_or_exporter_terminated':False,'completed_original_captures_modified':False}
(A/'expression-dispatcher-clean-drain.json').write_text(json.dumps(receipt,indent=2)+'\n')
try:
 for f in files:fcntl.flock(f,fcntl.LOCK_EX)
 # Both reader slots are now reserved after their actual readers exited.
 # Wait for the SAME driver's next queued helper, never terminate a Lean/lake.
 deadline=time.monotonic()+30
 while time.monotonic()<deadline:
  kids=subprocess.run(['ps','--ppid',str(driver),'-o','pid='],text=True,capture_output=True).stdout.split()
  for kid in kids:
   q=Path('/proc')/kid
   try:args=[x.decode()for x in(q/'cmdline').read_bytes().split(b'\0')if x];exe=(q/'comm').read_text().strip()
   except FileNotFoundError:continue
   if not any(x==str(runtime/'lean-probe.sh')for x in args):continue
   assert exe == 'bash',(kid,exe,args)
   grandkids=subprocess.run(['ps','--ppid',kid,'-o','pid='],text=True,capture_output=True).stdout.split()
   details=[]
   for g in grandkids:
    gp=Path('/proc')/g
    try:gexe=(gp/'comm').read_text().strip();ga=gp.joinpath('cmdline').read_bytes().decode().split('\0')
    except FileNotFoundError:continue
    assert gexe not in ['lean','lake','leanchecker'],(g,gexe,ga)
    details.append({'pid':int(g),'exe':gexe,'argv':ga})
   receipt.update(status='CANCELLED_ONLY_OWN_WAITING_READER_HELPER_AT_EMPTY_EXPORT_BOUNDARY',queued_probe_pid=int(kid),queued_probe_argv=args,queued_probe_exe=exe,queued_probe_children=details,time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
   os.kill(int(kid),signal.SIGTERM)
   (A/'expression-dispatcher-clean-drain.json').write_text(json.dumps(receipt,indent=2)+'\n')
   print(json.dumps(receipt));raise SystemExit(0)
  time.sleep(.05)
 raise RuntimeError('No own queued helper reached checkpoint; no process cancelled')
finally:
 for f in reversed(files):fcntl.flock(f,fcntl.LOCK_UN);f.close()
