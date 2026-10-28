#!/usr/bin/env python3
"""One new two-module capture; unchanged frozen serializer and comparator."""
from pathlib import Path
import collections
import gzip
import hashlib
import json
import os
import subprocess
import sys
import time

E = Path(__file__).resolve().parent
A = E.parent
D = A.parents[1]
N = Path('/workspace/hironaka-current-20261025/TranscendentalNakamaye')
plan = json.loads((E / 'plan.json').read_text())
original_plan = json.loads((A / 'plan.json').read_text())
rows = plan['whole_modules']
assert len(rows) == 2
O = E / 'full-expressions-attempt01'
O.mkdir(exist_ok=False)
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
serializer = A / 'frozen-tools/CanonicalStandaloneAllScopedOwnersV3.lean'
comparator = A / 'frozen-tools/compare_full_expr_dag.py'
assert sha(serializer) == original_plan['frozen_tools']['audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean']['sha256']
assert sha(comparator) == original_plan['frozen_tools']['audit/local-sharp-curves-20261015/compare_full_expr_dag.py']['sha256']

mapping = A / 'full-expressions-attempt01/exact-module-renames.tsv'
original_roster = O / 'original-modules.tsv'
public_roster = O / 'public-modules.tsv'
original_roster.write_text(''.join(row['source_module'] + '\t' + row['destination_module'] + '\n' for row in rows))
public_roster.write_text(''.join(row['destination_module'] + '\t' + row['destination_module'] + '\n' for row in rows))
inputs = {}
for row in rows:
    for base, module in [(N, row['source_module']), (D, row['destination_module'])]:
        relative = Path(*module.split('.'))
        for path in [base / relative.with_suffix('.lean'), base / '.lake/build/lib/lean' / relative.with_suffix('.olean')]:
            inputs[str(path)] = sha(path)
inputs[str(serializer)] = sha(serializer)
inputs[str(comparator)] = sha(comparator)
inputs[str(mapping)] = sha(mapping)
(O / 'before-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
command = [
    '/workspace/archon-nakamaye/work/lean-runtime/lean-probe.sh', 'flock', '-s',
    '/workspace/archon-nakamaye/work/lean-runtime/lean-build.lock',
    'lake', 'env', 'lean', '--run', str(serializer),
    str(original_roster), str(public_roster), str(mapping),
    str(O / 'original.jsonl'), str(O / 'public.jsonl'), str(O / 'actual-private-pairs.json'),
]
start = time.monotonic()
with (O / 'export.log').open('w') as log:
    result = subprocess.run(command, cwd=D, env=dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(N / '.lake/build/lib/lean')), stdout=log, stderr=subprocess.STDOUT)
(O / 'export.exit').write_text(str(result.returncode) + '\n')
assert result.returncode == 0
expected = {row['destination_module'] for row in rows}
captures = {}
for side in ['original', 'public']:
    target = O / side
    target.mkdir()
    groups = collections.defaultdict(list)
    with (O / (side + '.jsonl')).open('rb') as source:
        for line in source:
            obj = json.loads(line)
            assert obj['module'] in expected
            groups[obj['module']].append(line)
    assert set(groups) == expected
    captures[side] = {}
    for module, lines in groups.items():
        names = [json.loads(line)['name'] for line in lines]
        assert len(names) == len(set(names))
        output = target / (module + '.jsonl')
        output.write_bytes(b''.join(lines))
        compressed = output.with_suffix('.jsonl.gz')
        with compressed.open('wb') as raw, gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as dest:
            dest.write(output.read_bytes())
        captures[side][module] = {'actual_roots': len(lines), 'actual_names': names, 'raw_sha256': sha(output), 'gzip_sha256': sha(compressed)}
    (O / (side + '.jsonl')).unlink()

comparisons = {}
(O / 'comparisons').mkdir()
for module in sorted(expected):
    report = O / 'comparisons' / (module + '.json')
    with report.with_suffix('.log').open('w') as log:
        result = subprocess.run([sys.executable, str(comparator), str(O / 'original' / (module + '.jsonl')), str(O / 'public' / (module + '.jsonl')), str(report)], cwd=D, stdout=log, stderr=subprocess.STDOUT)
    check = json.loads(report.read_text())
    comparisons[module] = {'exit': result.returncode, 'status': check['status'], 'report': str(report.relative_to(E)), 'sha256': sha(report)}
    print(module, result.returncode, check['status'], flush=True)
for side in ['original', 'public']:
    for module in expected:
        (O / side / (module + '.jsonl')).unlink()
assert inputs == {path: sha(Path(path)) for path in inputs}
passed = all(row['exit'] == 0 and row['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH' for row in comparisons.values())
receipt = {
    'status': 'PASS_ALL2_WHOLE_TYPES_VALUES_PROOFS' if passed else 'BLOCKED_EXACT_DIFFERENCE_RETAINED',
    'native_revision': plan['native_revision'], 'new_whole_modules': 2,
    'source_artifact_inputs_unchanged': True, 'all_children_reaped': True,
    'frozen_serializer_sha256': sha(serializer), 'frozen_comparator_sha256': sha(comparator),
    'actual_module_mapping_sha256': sha(mapping), 'command': command,
    'captures': captures, 'comparisons': comparisons,
    'public_root_filters': 0, 'numeric_or_proof_name_rewrites': False,
    'old31_kernel_or_Expr_replay': False, 'seconds': time.monotonic() - start,
}
(O / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(receipt['status'], flush=True)
raise SystemExit(0 if passed else 1)
