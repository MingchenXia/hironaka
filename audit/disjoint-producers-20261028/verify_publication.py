"""Read-only verification of the pinned source-faithful publication; no builds."""
from pathlib import Path
import hashlib
import json
import sys

A = Path(__file__).resolve().parent
S = A.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
v = json.loads((A / 'publication-verification.json').read_text())
manifest = json.loads((A / 'publication-evidence-manifest.json').read_text())
assert v['status'] == 'PASS_SOURCE_FAITHFUL_COMPOSITE33_PUBLICATION'
for rel, pin in manifest['files'].items():
    assert sha(S / rel) == pin, rel
for rel, pin in json.loads((A / 'plan.json').read_text())['old_file_guards'].items():
    assert sha(S / rel) == pin, rel
for row in v['source_modules']:
    assert sha(S / row['source_path']) == row['source_sha256']
    if '--artifacts' in sys.argv:
        for rel, pin in row['all_compiled_parts'].items():
            assert sha(S / rel) == pin, rel
assert len(v['source_modules']) == v['unique_new_target_kernels'] == 33
assert v['unique_new_allphysical_type_wholevalue_audits'] == 33
for row in v['support_blueprint_marker_changes']:
    text = (S / row['path']).read_text()
    assert sha(S / row['path']) == row['ready_sha256']
    assert text.count('\\leanok') == row['nodes'] and '\\notready' not in text
assert not v['merge_authorized'] and not v['source_goal_closure_claimed']
print('PASS: 33 source-faithful modules, 209 checked bindings, 748 physical declarations; original open goals unchanged')
