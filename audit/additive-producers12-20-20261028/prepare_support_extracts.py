#!/usr/bin/env python3
"""Prepare two complete original declarations and honest local BP supplements."""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
E = Path(__file__).resolve().parent
D = E.parents[1]
A = D / 'audit/disjoint-producers-20261028'
plan = json.loads((E / 'plan.json').read_text())
R = Path(plan['native_source_checkout'])
sha = lambda data: hashlib.sha256(data).hexdigest()
spec = importlib.util.spec_from_file_location('support_frozen_names', A / 'frozen-tools/upstream_namespace_map.py')
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
scope = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
node = next(node for node in ast.parse((A / 'frozen-tools/verify_incremental_source.py').read_text()).body if isinstance(node, ast.FunctionDef) and node.name == 'relocate')
exec(compile(ast.Module(body=[node], type_ignores=[]), 'frozen-support-relocation', 'exec'), scope)
header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
records = []
specifications = [
    ('CodimOnePartCanonical', 'codimOnePartAlong_geoTransformAlong_of_wEquiv',
     'Hironaka.Support.CodimOneCanonicalEquivalenceOriginalExact',
     [(65, 84), (283, 286)], (345, 353), [(355, 356), (439, 441)]),
    ('CodimOnePartTowerAlong', 'codimOnePartAlong_geoTransformAlong_eq_empty',
     'Hironaka.Support.CodimOneTowerEmptyOriginalExact',
     [(59, 87)], (142, 151), [(153, 154), (373, 375)]),
]
for short, declaration, destination_module, prefix_ranges, declaration_range, suffix_ranges in specifications:
    module = 'TranscendentalNakamaye.Pending.' + short
    path = 'TranscendentalNakamaye/' + module.replace('.', '/') + '.lean'
    raw = subprocess.check_output(['git', '-C', str(R), 'show', plan['native_revision'] + ':' + path])
    assert raw == subprocess.check_output(['git', '-C', str(R), 'show', plan['frozen_native_base'] + ':' + path])
    lines = raw.decode().splitlines(keepends=True)
    selected = lambda span: ''.join(lines[span[0] - 1:span[1]])
    before = ''.join(selected(span) for span in prefix_ranges)
    declaration_text = selected(declaration_range)
    assert re.search(r'^theorem\s+' + declaration + r'\b', declaration_text, re.M)
    after = ''.join(selected(span) for span in suffix_ranges)
    context = before + declaration_text + '\n' + after
    original_import = names.new_mod(module)
    output = header + 'import ' + original_import + '\n\n'
    output += 'set_option autoImplicit false\nset_option linter.unusedSectionVars false\n\n'
    output += scope['relocate'](context)
    capture = 'support-original-parents/' + short + '.lean'
    parent = E / capture
    parent.parent.mkdir(exist_ok=True)
    assert not parent.exists()
    parent.write_bytes(raw)
    draft = 'draft-source/' + destination_module.split('.')[-1] + '.lean'
    target = E / draft
    assert not target.exists()
    target.write_text(output)
    destination = destination_module.replace('.', '/') + '.lean'
    assert not (D / destination).exists()
    records.append({
        'source_module': module, 'source_path': path, 'source_parent_capture': capture,
        'source_parent_sha256': sha(raw), 'original_import': original_import,
        'destination_module': destination_module, 'destination_path': destination,
        'draft_capture': draft, 'draft_sha256': sha(output.encode()),
        'destination_sha256': sha(output.encode()),
        'original_context_segments': [before, '\n' + after],
        'original_context_prefix_ranges': prefix_ranges, 'original_context_suffix_ranges': suffix_ranges,
        'selected_original_declarations': [{'original_name': module + '.' + declaration,
            'inclusive_lines': declaration_range, 'original_text': declaration_text,
            'sha256': sha(declaration_text.encode())}],
        'additional_pure_support_imports': [], 'administrative_elaboration_contexts': [],
        'source_type_proof_payload_changes': 0,
    })

bp_path = 'TranscendentalNakamaye/blueprint/src/blowup-calculus.tex'
bp_raw = subprocess.check_output(['git', '-C', str(R), 'show', plan['native_revision'] + ':' + bp_path])
assert bp_raw == subprocess.check_output(['git', '-C', str(R), 'show', plan['frozen_native_base'] + ':' + bp_path])
parent = E / 'support-original-parents/blowup-calculus.tex'
parent.write_bytes(bp_raw)
text = bp_raw.decode()
original_nodes = []
for record in records:
    original_name = record['selected_original_declarations'][0]['original_name']
    position = text.index(original_name)
    begins = list(re.finditer(r'\\begin\{(definition|lemma|theorem|proposition|corollary)\}', text[:position]))
    assert begins
    start = begins[-1].start()
    kind = begins[-1].group(1)
    end = text.index('\\end{' + kind + '}', position) + len('\\end{' + kind + '}')
    proof_start = text.index('\\begin{proof}', end)
    next_node = re.search(r'\\begin\{(?:definition|lemma|theorem|proposition|corollary)\}', text[end:])
    assert next_node is None or proof_start < end + next_node.start()
    proof_end = text.index('\\end{proof}', proof_start) + len('\\end{proof}')
    node = text[start:proof_end]
    assert node.count('\\begin{proof}') == node.count('\\end{proof}') == 1
    labels = re.findall(r'\\label\{([^}]+)\}', node)
    assert len(labels) == 1
    capture = 'original-support-blueprint-nodes/' + labels[0].replace(':', '-') + '.tex'
    target = E / capture
    target.parent.mkdir(exist_ok=True)
    target.write_text(node)
    original_nodes.append({'label': labels[0], 'source_path': bp_path,
        'source_revision': plan['native_revision'], 'source_parent_capture': str(parent.relative_to(E)),
        'source_parent_sha256': sha(bp_raw), 'source_label_line': text[:text.index('\\label{' + labels[0] + '}')].count('\n') + 1,
        'complete_original_node_and_proof_capture': capture, 'capture_sha256': sha(node.encode()),
        'original_native_attachments': [name.strip() for group in re.findall(r'\\lean\{([^}]+)\}', node) for name in group.split(',')],
        'original_node_preserved_as_provenance_not_added_as_broad_local_binding_claim': True})

bp = r'''\section{Original codimension-one history declarations restored for this export}

The existing standalone chapter records these two original declarations as
upstream-only. Their complete original source, section contexts, and original
native blueprint nodes and proofs at revision
\texttt{6e453e142420e6a64ccfdb5cadd15abc2379f581} are retained in the audit.
The following precise local attachments and complete written proofs complement
the existing chapter. They add no hypothesis, new mathematical result, or
resolution closure claim.

\begin{lemma}[Weak equivalence preserves the current codimension-one part]
\label{hir:additive-export-codim-equivalence-history}
\uses{bcalc:codim-one-part-canonical}
\lean{Hironaka.CodimOnePartCanonical.codimOnePartAlong_geoTransformAlong_of_wEquiv}
Let $M,L$ be weakly equivalent marked ideals on the same ambient manifold,
with the same underlying submanifold $N$. For every actual finite $M$-test
tower $T$, the codimension-one parts of $M_T$ and $L_T$ are equal.
No coherence, closedness, or equality of their marked ideals is assumed.
\end{lemma}
\begin{proof}
The transformed underlying submanifold is the strict transform along the
same physical tower of the original submanifold. Thus the equality of the
original submanifolds gives equality of the two current submanifolds.
Weak equivalence gives equality of the two current cosupports along this
same $M$-test tower. The codimension-one part depends only on the underlying
submanifold and that cosupport, so the congruence theorem for those two sets
gives the asserted equality.
\end{proof}

\begin{lemma}[An empty codimension-one part stays empty]
\label{hir:additive-export-codim-empty-history}
\uses{bcalc:codim-one-part-tower}
\lean{Hironaka.CodimOnePartTowerAlong.codimOnePartAlong_geoTransformAlong_eq_empty}
Let $M$ be well formed, of maximal order along its underlying submanifold,
with mark at least one and empty original codimension-one part. Along every
actual finite $M$-test tower $T$, its current codimension-one part is empty.
\end{lemma}
\begin{proof}
The codimension-one tower theorem puts the current codimension-one part
inside the inverse image, under the actual projection of $T$, of the
original codimension-one part. That original set is empty, so its inverse
image is empty. A subset of the empty set is empty, proving the claim.
\end{proof}
'''
bp_capture = 'draft-blueprint/additive-producers12-20-original-codim-support.tex'
(E / bp_capture).write_text(bp)
result = {'status': 'PREPARED_TWO_COMPLETE_ORIGINAL_SUPPORT_DECLARATIONS_AND_WRITTEN_PROOFS',
          'native_revision': plan['native_revision'], 'support_extracts': records,
          'original_blueprint_nodes': original_nodes,
          'local_written_BP_supplement': {'draft_capture': bp_capture,
              'draft_sha256': sha(bp.encode()),
              'destination_path': 'blueprint/additive-producers12-20-original-codim-support.tex',
              'complete_written_proofs': 2, 'literal_bindings': 2,
              'new_local_labels': 2, 'ready_markers': 0,
              'not_claimed_whole_original_BP_chapter': True},
          'old33_source_BP_artifacts_unchanged': True,
          'no_public_install': True, 'compiler_used_for_this_preparation': False}
assert not (E / 'support-extraction-plan.json').exists()
(E / 'support-extraction-plan.json').write_text(json.dumps(result, indent=2) + '\n')
print(result['status'])
