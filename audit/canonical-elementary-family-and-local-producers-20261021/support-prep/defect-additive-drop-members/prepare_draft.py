"""DRAFT ONLY: replay one complete original declaration and its full BP node.

No Lean, build, kernel, Expr, production-source or Git mutation is performed.
Only this support-prep directory is written.
"""
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
STANDALONE = Path('/workspace/hironaka')
NATIVE = Path('/workspace/archon-publish')
REV = '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
SOURCE = 'TranscendentalNakamaye/TranscendentalNakamaye/Pending/DropMembers.lean'
BLUEPRINT = 'TranscendentalNakamaye/blueprint/src/hironaka.tex'
NATIVE_NAME = 'TranscendentalNakamaye.Pending.DropMembers.isGeoTestTower_withE_iff_of_centresIn'
PUBLIC_NAME = 'Hironaka.DropMembers.isGeoTestTower_withE_iff_of_centresIn'
MODULE = 'Hironaka.Support.DropMembersContainingCentresOriginalExact'
sha = lambda b: hashlib.sha256(b).hexdigest()

def git_bytes(path):
    return subprocess.check_output(['git', '-C', str(NATIVE), 'show', REV + ':' + path])

def blob(path):
    return subprocess.check_output(['git', '-C', str(NATIVE), 'rev-parse', REV + ':' + path]).decode().strip()

def line_range(parent, payload):
    assert parent.count(payload) == 1
    begin = parent.index(payload)
    first = parent[:begin].count('\n') + 1
    return [first, first + len(payload.splitlines()) - 1]

def write(name, data):
    (HERE / name).write_bytes(data.encode() if isinstance(data, str) else data)

def write_json(name, data):
    write(name, json.dumps(data, indent=2, ensure_ascii=False) + '\n')

raw = git_bytes(SOURCE)
source = raw.decode()
bpraw = git_bytes(BLUEPRINT)
bp = bpraw.decode()
write('DropMembers.whole-original.lean.txt', raw)
original_imports = source[:source.index('\n\nset_option')]
write('original-imports.lean.txt', original_imports + '\n')

# Preserve precisely the original active contexts, excluding the already closed
# NC section and all earlier theorem declarations.
options = 'set_option autoImplicit false\nset_option linter.unusedSectionVars false\n'
opening = source[source.index('open Set Filter\n'):source.index('\n\n/-! ### Normal crossings')]
tower = 'section Tower\n\nvariable {n : ℕ} {X : CMfd.{u} n}\n'
closing = 'end Tower\n\nend\n\nend TranscendentalNakamaye.Pending.DropMembers\n'
for text in (options, opening, tower, closing):
    assert source.count(text) == 1
assert source.endswith(closing)
context = options + '\n' + opening + '\n\n' + tower
write('original-active-context.lean.txt', context)
write('original-balanced-closings.lean.txt', closing)

start = source.index('/-- **Deleting the members that contain every centre** (`hir:drop-containing-members`)')
end = source.index('\n\n/-- **Deleting members away from the cosupport**', start) + 1
selected = source[start:end]
assert selected.count('theorem isGeoTestTower_withE_iff_of_centresIn ') == 1
assert selected.endswith('.isSNCDivisor) hsub hA\n')
write('isGeoTestTower_withE_iff_of_centresIn.complete-original.lean.txt', selected)

# Execute only the established, frozen relocation function, never the verifier
# module's command-line entry point or any of its writes/runtime gates.
map_path = STANDALONE / 'scripts/upstream_namespace_map.py'
spec = importlib.util.spec_from_file_location('draft_namespace_names', map_path)
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
relocation_path = STANDALONE / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
tree = ast.parse(relocation_path.read_text())
relocate_def = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
env = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
exec(compile(ast.Module(body=[relocate_def], type_ignores=[]), str(relocation_path), 'exec'), env)
relocate = env['relocate']

imports = ['Hironaka.Invariant.DropMembers', 'Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism']
header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
draft = header + ''.join('import ' + m + '\n' for m in imports) + '\n' + relocate(context) + '\n' + relocate(selected) + '\n' + relocate(closing)
assert relocate(selected) == selected  # No names in this declaration need token relocation.
assert draft.count(selected) == 1
write('DropMembersContainingCentresOriginalExact.lean', draft)

# Static scope balance is deliberately separate from a future Lean check.
stack = []
for number, line in enumerate(draft.splitlines(), 1):
    if m := re.fullmatch(r'namespace (\S+)', line):
        stack.append(('namespace', m.group(1), number))
    elif line == 'noncomputable section':
        stack.append(('section', '', number))
    elif m := re.fullmatch(r'section (\S+)', line):
        stack.append(('section', m.group(1), number))
    elif m := re.fullmatch(r'end(?: (\S+))?', line):
        assert stack, (number, line)
        kind, name, begin = stack.pop()
        assert (m.group(1) or '') == name, (number, line, kind, name, begin)
assert not stack
assert not re.search(r'^\s*(include|omit|local\s+(?:instance|notation)|attribute\s+\[local)', context, re.M)

node_start = bp.index('\\begin{lemma}[Deleting the members that contain every centre]\n')
node_end = bp.index('\\end{proof}', node_start) + len('\\end{proof}\n')
node = bp[node_start:node_end]
assert node.count('\\begin{proof}') == node.count('\\end{proof}') == 1
assert node.count('\\label{hir:drop-containing-members}') == 1
bindings = re.findall(r'\\lean\{([^}]*)\}', node)
assert len(bindings) == 1
bindings = bindings[0].split(',')
assert bindings == [NATIVE_NAME + '_of_snc', NATIVE_NAME]
write('hir-drop-containing-members.complete-original-node.tex', node)
write('hir-drop-containing-members.relocated-reference-node.tex', names.rename_text_names(node))

coverage = []
for path in sorted((STANDALONE / 'blueprint').rglob('*.tex')):
    text = path.read_text()
    labels = re.findall(r'\\label\{hir:drop-containing-members\}', text)
    if labels:
        coverage.append({'path': str(path.relative_to(STANDALONE)), 'local_label_occurrences': len(labels)})
assert coverage == []

callees_path = Path('/workspace/archon-nakamaye/work/g1-g9-20261021-phase3/publication/native40-callee-preflight/native40-direct-callee-availability.json')
callee_edges = [x for x in json.loads(callees_path.read_text())['ordinary_absent_occurrences'] if x['native_callee'] == NATIVE_NAME]
assert len(callee_edges) == 2
assert all(x['actual_native_callee_lookup_owner'] == 'TranscendentalNakamaye.Pending.DropMembers' for x in callee_edges)

public_imports = []
for module in imports:
    path = STANDALONE / (module.replace('.', '/') + '.lean')
    assert path.is_file()
    public_imports.append({'module': module, 'path': str(path.relative_to(STANDALONE)), 'sha256': sha(path.read_bytes())})

audit = {
    'status': 'DRAFT_ONLY_COMPLETE_ORIGINAL_STATIC_EXTRACTION_PASS_NOT_BUILT',
    'fixed_ordinary_revision': REV,
    'ordinary_git_repository': str(NATIVE),
    'source_path': SOURCE,
    'source_git_blob_oid': blob(SOURCE),
    'source_sha256': sha(raw),
    'selected_original_declaration': NATIVE_NAME,
    'selected_complete_doc_statement_proof_lines': line_range(source, selected),
    'selected_complete_doc_statement_proof_sha256': sha(selected.encode()),
    'selected_original_payload': 'isGeoTestTower_withE_iff_of_centresIn.complete-original.lean.txt',
    'whole_original_copy': 'DropMembers.whole-original.lean.txt',
    'proposed_public_module': MODULE,
    'proposed_public_declaration': PUBLIC_NAME,
    'draft': 'DropMembersContainingCentresOriginalExact.lean',
    'draft_sha256': sha(draft.encode()),
    'draft_lines': len(draft.splitlines()),
    'draft_complete_original_declaration_byte_identical': True,
    'statement_or_proof_token_edits': 0,
    'context': {
        'original_imports': {'lines': line_range(source, original_imports), 'payload': original_imports},
        'options': {'lines': line_range(source, options), 'payload': options},
        'opens_universe_namespace_noncomputable': {'lines': line_range(source, opening), 'payload': opening},
        'tower_section_and_variables': {'lines': line_range(source, tower), 'payload': tower},
        'balanced_original_closings': {'lines': line_range(source, closing), 'payload': closing},
        'active_include_omit_local_instance_local_notation_or_local_attribute': [],
        'closed_NC_section_not_active_or_copied': True,
        'static_scope_stack_empty': True,
        'context_mutation_beyond_frozen_namespace_relocation': False,
    },
    'existing_public_imports': public_imports,
    'pure_import_justification': {
        imports[0]: 'Existing complete _of_snc theorem and original tower vocabulary.',
        imports[1]: 'Existing original well-formed-transform theorem used literally by this proof.'
    },
    'frozen_relocation': {'algorithm_path': str(relocation_path), 'algorithm_file_sha256': sha(relocation_path.read_bytes()), 'namespace_map_path': str(map_path), 'namespace_map_sha256': sha(map_path.read_bytes()), 'only_relocate_AST_executed': True},
    'actual_native_owner_metadata': {'path': str(callees_path), 'sha256': sha(callees_path.read_bytes()), 'edge_observations': callee_edges},
    'blueprint': {
        'source_path': BLUEPRINT, 'source_git_blob_oid': blob(BLUEPRINT), 'source_parent_sha256': sha(bpraw),
        'complete_original_node_lines': line_range(bp, node),
        'complete_original_node_sha256': sha(node.encode()),
        'complete_original_node': 'hir-drop-containing-members.complete-original-node.tex',
        'relocated_reference_only_node': 'hir-drop-containing-members.relocated-reference-node.tex',
        'proof_count': 1, 'proof_or_statement_edits': 0,
        'inherited_original_leanok_is_not_new_local_acceptance': True,
        'local_complete_node_coverage_in_current_blueprint': coverage,
        'external_anchor_preparation_only': 'additive40-external-index-preparation.json; fixed reference capture existed in additive40-frozen-preparation/reference-prerequisite-nodes/hir--drop-containing-members.tex',
        'all_original_attached_bindings': [
            {'native': bindings[0], 'public': names.rename_ns(bindings[0]), 'later_treatment': 'Existing local original theorem in Hironaka.Invariant.DropMembers; actual binding verification remains required.'},
            {'native': bindings[1], 'public': names.rename_ns(bindings[1]), 'later_treatment': 'This new exact support draft; local binding only after production owner integration and all actual gates.'}
        ],
        'uses': re.search(r'\\uses\{([^}]*)\}', node).group(1).split(','),
        'installation_or_master_edit': False,
    },
    'base323_sources_or_provenance_modified': False,
    'production_lean_blueprint_or_git_modified': False,
    'lean_build_kernel_expr_or_axiom_runtime_invoked': False,
    'remaining_gates': ['Separate full source/context/BP static peer.', 'Frontier-only integration after approval.', 'Actual Lean elaboration/build and owner/whole type/value/kernel/axiom/binding verification; no such PASS is asserted here.'],
}
write_json('extraction-audit.json', audit)
print(json.dumps({'status': audit['status'], 'draft_sha256': audit['draft_sha256'], 'original_range': audit['selected_complete_doc_statement_proof_lines'], 'blueprint_range': audit['blueprint']['complete_original_node_lines'], 'bp_bindings': bindings}, indent=2))
