from pathlib import Path
import hashlib
import json
import subprocess
import sys

A = Path(__file__).resolve().parent.parent
D = A.parents[1]
I = A / 'independent'
stage = sys.argv[1]
out = I / f'{stage}-release-pins.json'
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

if stage == 'before':
    baseline = I / 'before-base-pins.json'
    assert not baseline.exists()
    subprocess.run([sys.executable, str(I / 'capture_pins.py'), baseline.name], check=True)
    rows = json.loads(baseline.read_text())
    plan = json.loads((A / 'plan.json').read_text())
    freeze = json.loads((A / 'public31-release-freeze-final.json').read_text())
    paths = set(rows)
    paths.update(freeze['all_source_BP_root_master_compiled_input_pins'])
    paths.update(plan['old_file_guards'])
    paths.add(str((A / 'public31-release-freeze-final.json').relative_to(D)))
    for row in freeze['all31_strict_full_types_values_proofs'].values():
        path = A / row['report']
        assert sha(path) == row['sha256']
        paths.add(str(path.relative_to(D)))
    paths.update(str(p.relative_to(D)) for p in I.glob('*.py'))
    paths.update(str(p.relative_to(D)) for p in I.glob('*.lean'))
    for path, expected in plan['old_file_guards'].items():
        assert sha(D / path) == expected, path
else:
    rows = json.loads((I / 'before-release-pins.json').read_text())
    paths = set(rows)

rows = {p: {'sha256': sha(D / p), 'bytes': (D / p).stat().st_size}
        for p in sorted(paths)}
out.write_text(json.dumps(rows, indent=2) + '\n')
if stage != 'before':
    before = json.loads((I / 'before-release-pins.json').read_text())
    assert rows == before, [p for p in rows if rows[p] != before[p]]
print(stage, len(rows), 'UNCHANGED' if stage != 'before' else 'PINNED')
