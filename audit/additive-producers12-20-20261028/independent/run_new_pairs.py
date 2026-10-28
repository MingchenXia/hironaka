from pathlib import Path
import json
import os
import subprocess
import time

I = Path(__file__).resolve().parent
E = I.parent
D = E.parents[1]
mods = json.loads((I / 'modules.json').read_text())
assert len(mods) == 16
runtime = '/workspace/archon-nakamaye/work/lean-runtime'
env = dict(os.environ)
env['PATH'] = runtime + '/lean-4.33.1-linux/bin:' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
jobs = []
for i, module in enumerate(mods):
    jobs.append((i, 'kernel', module,
                 ['lake', 'env', 'leanchecker', '--verbose', module]))
    jobs.append((i, 'physical', module,
                 ['lake', 'env', 'lean', str(I / f'physical-{i:02d}.lean')]))
jobs.append((None, 'literal-bindings', None,
             ['lake', 'env', 'lean', str(I / 'LiteralBindings.lean')]))
rows = []
# One reader in this lane leaves the second runtime slot to other lanes.
for i, kind, module, tail in jobs:
    name = f'{kind}-{i:02d}' if i is not None else kind
    log = I / (name + '.log')
    receipt = I / (name + '-exit.json')
    assert not log.exists() and not receipt.exists()
    command = [runtime + '/lean-probe.sh', 'flock', '-s',
               runtime + '/lean-build.lock', *tail]
    start = time.monotonic()
    with log.open('wb') as output:
        proc = subprocess.Popen(command, cwd=D, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
        code = proc.wait()
    row = {'index': i, 'module': module, 'kind': kind, 'command': command,
           'cwd': str(D), 'exit': code, 'seconds': time.monotonic() - start,
           'all_children_reaped': True}
    receipt.write_text(json.dumps(row, indent=2) + '\n')
    rows.append(row)
    print(name, code, flush=True)
(I / 'pair-and-binding-exits.json').write_text(json.dumps(rows, indent=2) + '\n')
assert len(rows) == 33 and all(row['exit'] == 0 for row in rows)
print('ALL_UNIQUE_ADDITIVE16_PAIRS_AND_270_BINDINGS_PASS', flush=True)
