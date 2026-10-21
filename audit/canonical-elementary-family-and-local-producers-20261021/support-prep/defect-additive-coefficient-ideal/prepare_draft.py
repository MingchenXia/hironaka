"""DRAFT ONLY complete-original CoefficientIdeal9 extraction, without Lean."""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = Path('/workspace/hironaka')
A = ROOT / 'audit/canonical-elementary-family-and-local-producers-20261021'
NATIVE = Path('/workspace/archon-publish')
REV = '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
FINAL = '47cef49895832e3bfe492f66e1f2ac68785187dd'
SOURCE = 'TranscendentalNakamaye/TranscendentalNakamaye/Pending/CoefficientIdeal.lean'
BP = 'TranscendentalNakamaye/blueprint/src/maximal-contact.tex'
PARENT = 'TranscendentalNakamaye.Pending.CoefficientIdeal'
MODULE = 'Hironaka.Support.CoefficientIdealTowerOperationsOriginalExact'
CLOSURE = Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication/native8-recursive-callee-closure/ordinary-source-declarations-by-parent.json')
sha = lambda b: hashlib.sha256(b).hexdigest()

def show(path, rev=REV):
    return subprocess.check_output(['git', '-C', str(NATIVE), 'show', rev + ':' + path])

def oid(path):
    return subprocess.check_output(['git', '-C', str(NATIVE), 'rev-parse', REV + ':' + path]).decode().strip()

def write(path, data):
    path = HERE / path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data.encode() if isinstance(data, str) else data)

raw = show(SOURCE)
assert show(SOURCE, FINAL) == raw
source = raw.decode()
lines = source.splitlines(keepends=True)
bpraw = show(BP)
assert show(BP, FINAL) == bpraw
bp = bpraw.decode()
write('CoefficientIdeal.whole-original.lean.txt', raw)
write('maximal-contact.whole-original.tex.txt', bpraw)

def segment(lo, hi):
    return ''.join(lines[lo - 1:hi])

def line_range(parent, payload):
    assert parent.count(payload) == 1
    first = parent[:parent.index(payload)].count('\n') + 1
    return [first, first + len(payload.splitlines()) - 1]

selected_ranges = {
    'finSumIdeal_le': [78, 82],
    'controlledTransform_finSumIdeal': [113, 136],
    'cosupp_msum': [182, 199],
    'isAdmissibleCentre_msum_iff': [201, 209],
    'geoTransform_msum': [214, 240],
    'IsAmbientFamily.geoTransform': [242, 252],
    'geoTransformAlong_msum': [262, 297],
    'derivMarked_zero': [301, 304],
    'coeff_tower': [322, 360],
}
roster = next(x for x in json.loads(CLOSURE.read_text()) if x['actual_native_parent'] == PARENT)
assert roster['whole_source_sha256'] == sha(raw)
assert {x['actual_original_declaration'] for x in roster['complete_ordinary_original_declarations']} == {PARENT + '.' + k for k in selected_ranges}
payloads = {}
for name, (lo, hi) in selected_ranges.items():
    body = segment(lo, hi)
    assert body.startswith('/--')
    declaration = next(x for x in roster['complete_ordinary_original_declarations'] if x['actual_original_declaration'] == PARENT + '.' + name)
    assert lines[declaration['source_line'] - 1].rstrip('\n') == declaration['exact_original_heading']
    assert body.count('theorem ' + name + ' ') == 1
    assert source.count(body) == 1
    payloads[name] = body
    write('original-declarations/' + name + '.lean.txt', body)

map_path = ROOT / 'scripts/upstream_namespace_map.py'
spec = importlib.util.spec_from_file_location('coefficient_draft_names', map_path)
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
relocation_path = ROOT / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
tree = ast.parse(relocation_path.read_text())
relocate_def = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
env = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
exec(compile(ast.Module(body=[relocate_def], type_ignores=[]), str(relocation_path), 'exec'), env)
relocate = env['relocate']

context_ranges = {
    'original_imports': [1, 3], 'options': [5, 6],
    'shared_opens_universe_namespace_noncomputable': [36, 47],
    'FinSum_section_variables': [51, 54], 'FinSum_blowup_variables': [110, 111], 'FinSum_end': [138, 138],
    'MSum_section_variables': [142, 144], 'MSum_manifold_instance': [168, 168],
    'MSum_family_variables': [177, 177], 'MSum_blowup_variables': [211, 212], 'MSum_end': [254, 254],
    'Tower_section_variables': [258, 260], 'balanced_final_closings': [362, 366],
}
contexts = {name: segment(*interval) for name, interval in context_ranges.items()}
for name, text in contexts.items():
    write('original-context/' + name + '.lean.txt', text)
assert not re.search(r'^\s*(include|omit|local\s+(?:instance|notation)|attribute\s+\[local)', source, re.M)

imports = ['Hironaka.MarkedIdeal.CoefficientIdeal', 'Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact',
           'Hironaka.Support.MarkedIdealOperationsMonotoneControlledOriginalExact',
           'Hironaka.Support.OrderMultiplicativityCosupportOriginalExact',
           'Hironaka.Support.DerivativeIdealTowerOriginalExact']
support_drafts = {
    imports[2]: A / 'support-prep/canonical-additive-marked-operations/MarkedIdealOperationsMonotoneControlledOriginalExact.lean',
    imports[3]: A / 'support-prep/setup-additive-order-powers/OrderMultiplicativityCosupportOriginalExact.lean',
    imports[4]: A / 'support-prep/tangent-additive-derivative-tower/DerivativeIdealTowerOriginalExact.lean',
}
ordered = [contexts['options'], contexts['shared_opens_universe_namespace_noncomputable'],
           contexts['FinSum_section_variables'], payloads['finSumIdeal_le'],
           contexts['FinSum_blowup_variables'], payloads['controlledTransform_finSumIdeal'], contexts['FinSum_end'],
           contexts['MSum_section_variables'], contexts['MSum_manifold_instance'], contexts['MSum_family_variables'],
           payloads['cosupp_msum'], payloads['isAdmissibleCentre_msum_iff'], contexts['MSum_blowup_variables'],
           payloads['geoTransform_msum'], payloads['IsAmbientFamily.geoTransform'], contexts['MSum_end'],
           contexts['Tower_section_variables'], payloads['geoTransformAlong_msum'], payloads['derivMarked_zero'],
           payloads['coeff_tower'], contexts['balanced_final_closings']]
header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
draft = header + ''.join('import ' + m + '\n' for m in imports) + '\n' + relocate('\n'.join(ordered))
for body in payloads.values():
    assert relocate(body) == body
    assert draft.count(body) == 1
stack = []
for no, line in enumerate(draft.splitlines(), 1):
    if m := re.fullmatch(r'namespace (\S+)', line): stack.append(('namespace', m.group(1), no))
    elif line == 'noncomputable section': stack.append(('section', '', no))
    elif m := re.fullmatch(r'section (\S+)', line): stack.append(('section', m.group(1), no))
    elif m := re.fullmatch(r'end(?: (\S+))?', line):
        assert stack, (no, line)
        item = stack.pop()
        assert item[1] == (m.group(1) or ''), (no, line, item)
assert not stack
write('CoefficientIdealTowerOperationsOriginalExact.lean', draft)

labels = ['mc:finite-sum', 'mc:marked-finite-sum', 'mc:marked-finite-sum-tower', 'mc:coefficient-ideal', 'mc:coefficient-equivalent']
bp_records = []
existing_ambient = {'IsAmbientFamily', 'IsAmbientFamily.isCoherent_msum', 'coeffMarked', 'isAmbientFamily_derivMarked'}
for label in labels:
    label_pos = bp.index('\\label{' + label + '}')
    begin = list(re.finditer(r'\\begin\{(lemma|definition)\}', bp[:label_pos]))[-1]
    kind = begin.group(1)
    statement_end = bp.index('\\end{' + kind + '}', label_pos) + len('\\end{' + kind + '}\n')
    end = statement_end
    has_proof = bp[end:].lstrip().startswith('\\begin{proof}')
    if has_proof: end = bp.index('\\end{proof}', end) + len('\\end{proof}\n')
    node = bp[begin.start():end]
    assert node.count('\\begin{proof}') == node.count('\\end{proof}') == int(has_proof)
    original_bindings = [s for m in re.finditer(r'\\lean\{([^}]*)\}', node) for s in m.group(1).split(',')]
    node_name = label.replace(':', '--') + '.complete-original-node.tex'
    write('blueprint-original-nodes/' + node_name, node)
    coverage = []
    for path in sorted((ROOT / 'blueprint').rglob('*.tex')):
        text = path.read_text()
        if '\\label{' + label + '}' in text:
            coverage.append({'path': str(path.relative_to(ROOT)),
                             'status': 'EXTERNAL_SOURCE_ANCHOR_ONLY' if 'external-prerequisite' in path.name else 'LOCAL_LABEL_REQUIRES_COMPLETE_NODE_COMPARISON',
                             'source_sha256': sha(path.read_bytes())})
    attachments = []
    for original in original_bindings:
        assert original.startswith(PARENT + '.')
        short = original[len(PARENT) + 1:]
        if short in selected_ranges: owner = MODULE; status = 'NEW_EXACT_DRAFT_PENDING_ALL_GATES'
        else:
            owner = imports[1] if short in existing_ambient else imports[0]
            status = 'EXISTING_LOCAL_ORIGINAL_SOURCE_PENDING_BINDING_RECHECK'
        attachments.append({'original': original, 'relocated': names.rename_ns(original), 'proposed_local_owner': owner, 'status': status})
    bp_records.append({'label': label, 'environment': kind, 'original_lines': line_range(bp, node),
                       'node_sha256': sha(node.encode()), 'payload': 'blueprint-original-nodes/' + node_name,
                       'complete_written_proof_count': int(has_proof), 'proof_or_statement_edits': 0,
                       'all_original_attached_bindings': attachments,
                       'selected_nine_attached_here': [x['original'] for x in attachments if x['proposed_local_owner'] == MODULE],
                       'uses': re.search(r'\\uses\{([^}]*)\}', node).group(1).split(','),
                       'current_blueprint_coverage': coverage})
assert len(bp_records) == 5 and sum(r['complete_written_proof_count'] for r in bp_records) == 4
assert sum(len(r['all_original_attached_bindings']) for r in bp_records) == 21
assert {n for r in bp_records for n in r['selected_nine_attached_here']} == {PARENT + '.' + s for s in selected_ranges}
start = bp.index('\\subsection{Sums of marked ideals and the coefficient ideal}')
end = bp.index('\\subsection{Restriction of the coefficient ideal to a submanifold}', start)
section = bp[start:end]
assert section.count('\\begin{proof}') == section.count('\\end{proof}') == 4
write('blueprint-original-complete-subsection.tex', section)

dependency_records = []
for module in imports:
    p = ROOT / (module.replace('.', '/') + '.lean') if module not in support_drafts else support_drafts[module]
    dependency_records.append({'module': module, 'source_or_draft': str(p), 'exists_at_draft_capture': p.is_file(),
                               'sha256': sha(p.read_bytes()) if p.is_file() else None,
                               'status': 'EXISTING_PUBLIC_SOURCE' if module not in support_drafts else 'SEPARATELY_OWNED_AUTHENTIC_NEW_SUPPORT_DRAFT_NOT_INSTALLED'})
audit = {
    'status': 'DRAFT_ONLY_NINE_COMPLETE_ORIGINAL_DECLARATIONS_STATIC_PASS_NOT_BUILT',
    'fixed_ordinary_revision': REV, 'also_byte_identical_revision': FINAL, 'ordinary_git_repository': str(NATIVE),
    'actual_native_owner': PARENT, 'source_path': SOURCE, 'source_git_blob_oid': oid(SOURCE),
    'whole_source_sha256': sha(raw), 'whole_original_copy': 'CoefficientIdeal.whole-original.lean.txt',
    'canonical_closed40_roster': {'path': str(CLOSURE), 'sha256': sha(CLOSURE.read_bytes()), 'selected_parent_roster': roster},
    'proposed_public_module': MODULE, 'draft': 'CoefficientIdealTowerOperationsOriginalExact.lean',
    'draft_sha256': sha(draft.encode()), 'draft_lines': len(draft.splitlines()),
    'complete_original_declarations': [{'original_name': PARENT + '.' + key, 'public_name': names.rename_ns(PARENT + '.' + key),
        'original_lines_including_full_doc_statement_proof': selected_ranges[key], 'complete_payload_sha256': sha(value.encode()),
        'payload': 'original-declarations/' + key + '.lean.txt', 'draft_complete_payload_byte_identical': True,
        'statement_or_proof_token_edits': 0} for key, value in payloads.items()],
    'context': [{'name': name, 'original_lines': context_ranges[name], 'payload_sha256': sha(text.encode()),
                 'payload_file': 'original-context/' + name + '.lean.txt'} for name, text in contexts.items()],
    'active_original_include_omit_local_instance_local_notation_or_local_attribute': [],
    'all_original_sections_and_namespace_closings_balanced': True,
    'public_and_proposed_pure_imports': dependency_records,
    'blueprint': {'source_path': BP, 'source_git_blob_oid': oid(BP), 'source_parent_sha256': sha(bpraw),
                  'whole_parent_capture': 'maximal-contact.whole-original.tex.txt',
                  'complete_original_subsection': 'blueprint-original-complete-subsection.tex',
                  'complete_subsection_original_lines': line_range(bp, section), 'complete_subsection_sha256': sha(section.encode()),
                  'complete_nodes': bp_records, 'full_attached_binding_observations': 21, 'written_proofs': 4,
                  'original_definition_without_attached_written_proof': 'mc:coefficient-ideal',
                  'inherited_original_leanok_is_not_new_local_acceptance': True,
                  'no_node_attachment_or_proof_removed': True, 'installation_or_master_edit': False},
    'frozen_relocation': {'path': str(relocation_path), 'sha256': sha(relocation_path.read_bytes()),
                          'namespace_map_path': str(map_path), 'namespace_map_sha256': sha(map_path.read_bytes()),
                          'only_relocate_AST_executed': True},
    'base323_old_sources_or_provenance_modified': False, 'production_lean_blueprint_or_git_modified': False,
    'lean_build_kernel_expr_or_axiom_runtime_invoked': False,
    'remaining_gates': ['Separate full source/context/BP static peer.', 'Frontier-only authorized integration of the mutually disjoint support drafts.',
                        'Fresh actual source/owner/build/type-value/kernel/axiom/binding gates; no runtime acceptance is asserted.'],
}
write('extraction-audit.json', json.dumps(audit, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': audit['status'], 'draft_sha256': audit['draft_sha256'], 'draft_lines': audit['draft_lines'],
                  'complete_original_declarations': len(payloads), 'original_BP_nodes': len(bp_records),
                  'complete_written_proofs': 4, 'full_binding_observations': 21,
                  'separately_owned_import_drafts': dependency_records[2:]}, ensure_ascii=False, indent=2))
