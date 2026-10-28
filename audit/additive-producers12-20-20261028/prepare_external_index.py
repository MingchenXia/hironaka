#!/usr/bin/env python3
"""Prepare complete original external nodes and a documentation-only draft."""
from pathlib import Path
import hashlib
import json
import re

E = Path(__file__).resolve().parent
plan = json.loads((E / 'plan.json').read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
records = []
for row in plan['external_original_reference_parent_captures']:
    text = (E / row['source_parent_capture']).read_text()
    assert sha(text.encode()) == row['source_parent_sha256']
    label = row['label']
    needle = '\\label{' + label + '}'
    assert text.count(needle) == 1
    position = text.index(needle)
    begins = list(re.finditer(r'\\begin\{(definition|lemma|theorem|proposition|corollary)\}', text[:position]))
    assert begins, label
    start = begins[-1].start()
    kind = begins[-1].group(1)
    end = text.index('\\end{' + kind + '}', position) + len('\\end{' + kind + '}')
    next_node = re.search(r'\\begin\{(?:definition|lemma|theorem|proposition|corollary)\}', text[end:])
    limit = len(text) if next_node is None else end + next_node.start()
    proof = re.search(r'\\begin\{proof\}', text[end:limit])
    assert proof, ('Expected complete original proof', label)
    proof_end = text.index('\\end{proof}', end + proof.start()) + len('\\end{proof}')
    assert proof_end <= limit
    node = text[start:proof_end]
    capture = 'external-native-nodes/' + label.replace(':', '-') + '.tex'
    path = E / capture
    path.parent.mkdir(exist_ok=True)
    assert not path.exists()
    path.write_text(node)
    records.append({
        **{key: value for key, value in row.items() if key != 'complete_node_capture_and_honest_external_index_pending'},
        'complete_native_node_capture': capture,
        'complete_native_node_sha256': sha(node.encode()),
        'native_source_attachments': [name.strip() for group in re.findall(r'\\lean\{([^}]+)\}', node) for name in group.split(',') if name.strip()],
        'original_proof_complete': True,
    })
lines = [
    '\\section{External native prerequisites for the additive producers}',
    'These anchors point to complete original statements and proofs at native',
    'revision \\texttt{' + plan['native_revision'] + '}. They are external',
    'documentation prerequisites; they make no additional local theorem export',
    'or local kernel verification claim. Original parents, complete nodes and',
    'proofs, source lines, and original declaration attachments are retained',
    'in the audit.',
    '\\begin{description}',
]
for row in records:
    url = 'https://github.com/MingchenXia/archon-nakamaye/blob/' + plan['native_revision'] + '/' + row['source_path'] + '#L' + str(row['source_label_line'])
    lines += ['\\item[\\texttt{' + row['label'] + '}]\\label{' + row['label'] + '}', '\\href{' + url + '}{Fixed original native statement and proof}.']
lines += ['\\end{description}', '']
output = '\n'.join(lines)
capture = 'draft-blueprint/additive-producers12-20-native-prerequisites-20261028.tex'
target = E / capture
assert not target.exists()
target.write_text(output)
receipt = {
    'status': 'PREPARED4_COMPLETE_ORIGINAL_EXTERNAL_NODES_AND_PROOFS',
    'native_revision': plan['native_revision'], 'anchors': records,
    'draft_capture': capture, 'draft_sha256': sha(output.encode()),
    'local_lean_bindings': 0, 'local_ready_claims': 0,
    'no_public_BP_install': True, 'compiler_used': False,
}
(E / 'external-prerequisite-plan.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(receipt['status'])
