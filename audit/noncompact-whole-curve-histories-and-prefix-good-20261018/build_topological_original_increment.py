"""Compile the new dependency DAG serially, then run the configured full build.

The 16 GiB shared executor also runs three mathematical lanes. Serial incremental
targets prevent dozens of new Lean processes from competing for that memory.
No Lean proof or resource option is changed.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, time

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
OLD = A / 'previous-public-source-digests.json'
old = json.loads(OLD.read_text())['mathematical_sources']
assert len(old) == 1140
for name, digest in old.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
new = {str(p.relative_to(ROOT)).removesuffix('.lean').replace('/', '.'): p
       for p in sorted((ROOT / 'Hironaka').rglob('*.lean'))
       if str(p.relative_to(ROOT)) not in old}
assert len(new) == 19, len(new)
seen, active, ordered = set(), set(), []
def visit(module):
    if module in seen:
        return
    assert module not in active, ('New import cycle', module)
    active.add(module)
    for name in re.findall(r'^import\s+(Hironaka[\w.]*)', new[module].read_text(), re.M):
        if name in new:
            visit(name)
        else:
            assert (ROOT / (name.replace('.', '/') + '.lean')).is_file(), (module, name)
    active.remove(module)
    seen.add(module)
    ordered.append(module)
for module in new:
    visit(module)
(A / 'all-new-public-module-targets.json').write_text(json.dumps(ordered, indent=2) + '\n')
env = os.environ.copy()
env['PATH'] = '/workspace/lean-toolchains/lean-4.33.1-linux/bin:' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
rows = []
start = time.monotonic()
for index, module in enumerate(ordered, 1):
    log = A / f'incremental-build-{index:02}-{module.split(".")[-1]}.log'
    begin = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(['lake', 'build', '--wfail', module], cwd=ROOT, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    row = {'index': index, 'module': module, 'exit_code': result.returncode,
           'elapsed_seconds': round(time.monotonic() - begin, 3), 'log': log.name}
    rows.append(row)
    (A / 'serial-incremental-build-results.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(json.dumps(row), flush=True)
    if result.returncode:
        (A / f'failed-source-{index:02}-{module.split(".")[-1]}.lean.txt').write_bytes(new[module].read_bytes())
        raise SystemExit(result.returncode)
with (A / 'build-full-major443.log').open('w') as stream:
    result = subprocess.run(['lake', 'build', '--wfail'], cwd=ROOT, env=env,
                            stdout=stream, stderr=subprocess.STDOUT)
receipt = {'status': 'PASS_SERIAL_INCREMENT_AND_CONFIGURED_FULL_BUILD' if not result.returncode else 'FAILED_CONFIGURED_FULL_BUILD',
           'new_modules': len(new), 'exit_code': result.returncode,
           'elapsed_seconds': round(time.monotonic() - start, 3),
           'serial_incremental_targets': True, 'lean_num_threads': 1,
           'proof_resource_options_changed': False}
(A / 'major443-build-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
raise SystemExit(result.returncode)
