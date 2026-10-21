#!/usr/bin/env python3
"""Read-only source-generation gate; no Lean/Expr/kernel/parser-type claim.

Seven entire fixed ordinary source parents are replayed through the unchanged
release header/import/namespace relocation and recorded administrative contexts.
All fourteen notation clauses and their variable/include contexts stay literal.
Future actual public context commands require a new explicitly named receipt.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REV = '47cef49895832e3bfe492f66e1f2ac68785187dd'
SOURCE = Path('/workspace/archon-publish')
STANDALONE = Path('/workspace/hironaka')
PRINCIPAL = STANDALONE / 'audit/canonical-elementary-family-and-local-producers-20261021/support-prep/principal-parts/verify_three_notation_source_generation_after04.py'
RELOCATION = STANDALONE / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
PARENTS = {
    'HironakaActualDirectionalNormalJet': 2,
    'HironakaActualExceptionalJetHSComparison': 2,
    'HironakaActualExceptionalJetRigidity': 2,
    'HironakaActualInitialPivotNormality': 2,
    'HironakaActualPointNormalizedCoefficientBands': 3,
    'HironakaActualPointOrderRetainingHS': 2,
    'HironakaActualZeroPointReducedTail': 1,
}
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def notation_context(text, expected):
    lines = text.splitlines(keepends=True)
    at = [i for i, line in enumerate(lines) if line.startswith('local notation ')]
    require(len(at) == expected, 'Wrong literal notation count')
    contexts = [i for i in range(at[0]) if re.match(r'^(?:variable|include|omit)\b', lines[i])]
    require(bool(contexts), 'No original variable/include context')
    start = max(contexts)
    return ''.join(lines[start:at[-1] + 1])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--public-root', type=Path, default=HERE / 'candidate')
    p.add_argument('--contexts', type=Path, help='Explicit later approved per-module edits/imports JSON; never inferred')
    p.add_argument('--receipt', type=Path, default=HERE / 'seven-notation-source-generation-initial.json')
    args = p.parse_args()
    require(args.receipt.resolve().is_relative_to(HERE), 'Evidence writes restricted to offline preparation directory')
    profiles = json.loads((HERE / 'input-fingerprints.json').read_text())['standalone_frozen_inputs']
    for path in ['scripts/upstream_namespace_map.py', str(RELOCATION.relative_to(STANDALONE))]:
        require(sha((STANDALONE / path).read_bytes()) == profiles[path]['sha256'], 'Frozen relocation profile changed: ' + path)
    require(subprocess.check_output(['git', '-C', str(SOURCE), 'cat-file', '-t', REV]).strip() == b'commit', 'Missing fixed ordinary commit')
    sys.path.insert(0, str(STANDALONE / 'scripts'))
    import upstream_namespace_map as names
    names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
    flat = names.flattened_short()
    fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
    fn = next(n for n in ast.parse(RELOCATION.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
    scope = {'names': names, 'flat': flat, 'fq': fq, 're': re}
    exec(compile(ast.Module(body=[fn], type_ignores=[]), str(RELOCATION), 'exec'), scope)
    tree = ast.parse((HERE / 'frozen-inputs/sync_frozen_sources.py').read_text())
    header = ast.literal_eval(next(n.value for n in tree.body if isinstance(n, ast.Assign)
        and any(isinstance(t, ast.Name) and t.id == 'HEADER' for t in n.targets)))
    provenance = json.loads((HERE / 'module-provenance-plan.json').read_text())
    approved = json.loads(args.contexts.read_text()) if args.contexts else {}
    parents = []
    for stem, count in PARENTS.items():
        owner = 'TranscendentalNakamaye.Pending.' + stem
        rows = [r for r in provenance if r['source_module'] == owner]
        require(len(rows) == 1, 'Nonunique whole source provenance: ' + stem)
        row = rows[0]
        raw = subprocess.check_output(['git', '-C', str(SOURCE), 'show', REV + ':' + row['source_path']])
        require(sha(raw) == row['source_sha256'], 'Changed entire fixed source: ' + stem)
        original = raw.decode(); initial = header + scope['relocate'](original)
        require(sha(initial.encode()) == row['destination_sha256'], 'Changed initial frozen whole relocation: ' + stem)
        admin = approved.get(owner, {'administrative_elaboration_contexts': [], 'additional_pure_support_imports': []})
        edits = admin['administrative_elaboration_contexts']; extras = admin['additional_pure_support_imports']
        expected = initial
        for edit in edits:
            require(expected.count(edit['before']) == 1, 'Nonunique genuine context anchor')
            require(expected.index(edit['before']) > expected.rindex('local notation '), 'Context edit touches notation scope')
            require(edit['after'].endswith(edit['before']), 'Context must prepend an explicit command to unchanged original payload')
            prefix = edit['after'][:-len(edit['before'])]
            require(not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|instance|axiom|opaque|structure|class)\b', prefix, re.M), 'Context contains a new declaration')
            expected = expected.replace(edit['before'], edit['after'])
        if extras:
            first = re.search(r'^import ', expected, re.M); require(first is not None, 'No original import anchor')
            expected = expected[:first.start()] + ''.join('import ' + m + '\n' for m in extras) + expected[first.start():]
        public_path = args.public_root / row['destination_path']
        public = public_path.read_bytes()
        require(public == expected.encode(), 'ENTIRE public source differs from exact replay: ' + stem)
        orig_notation = [line for line in original.splitlines() if line.startswith('local notation ')]
        public_notation = [line for line in public.decode().splitlines() if line.startswith('local notation ')]
        require(orig_notation == public_notation and len(orig_notation) == count, 'Literal notation clause changed')
        context = notation_context(original, count)
        require(context == notation_context(public.decode(), count), 'Literal notation variable/include context changed')
        parents.append({'source_module': owner, 'destination_module': row['destination_module'],
            'fixed_original_source_path': row['source_path'], 'fixed_original_source_sha256': sha(raw),
            'entire_public_path': str(public_path), 'entire_public_sha256': sha(public),
            'initial_frozen_relocation_sha256': sha(initial.encode()), 'entire_source_replay_exact': True,
            'literal_local_notation_count': count, 'literal_local_notations': orig_notation,
            'literal_variable_include_context': context, 'literal_variable_include_context_sha256': sha(context.encode()),
            'recorded_administrative_contexts': edits, 'recorded_support_imports': extras})
    report = {'status': 'PASS_OFFLINE_BOUNDED_WHOLE_SOURCE_GENERATION_ONLY',
        'fixed_ordinary_revision': REV, 'public_root': str(args.public_root), 'complete_original_parents': 7,
        'exact_literal_notation_clauses': 14, 'parents': parents,
        'expected_frontend_definition_target_pending_actual_types': 42,
        'actual_42_original_or_public_typed_witness_gate_passed': False,
        'actual_generated_definition_count_confirmed_here': None,
        'parser_macro_unexpander_type_or_body_classification_claimed': False,
        'whole_environment_no_dependents_claimed': False, 'whole_mathematical_type_value_equality_claimed': False,
        'kernel_or_axiom_or_binding_pass_claimed': False, 'roots_erased_renamed_or_filtered': 0,
        'Lean_processes_or_Expr_exports_run': 0, 'production_source_changes': False,
        'replay_rule': 'Entire fixed ordinary source + frozen release header/import/namespace relocation + explicitly recorded administrative contexts/imports only.',
        'later_context_updates_require_new_receipt_and_full_byte_replay': True,
        'design_witness': {'path': str(PRINCIPAL), 'sha256': sha(PRINCIPAL.read_bytes())},
        'frozen_relocation': {'path': str(RELOCATION), 'sha256': sha(RELOCATION.read_bytes())},
        'namespace_map_sha256': sha((STANDALONE / 'scripts/upstream_namespace_map.py').read_bytes()),
        'approved_context_input': None if not args.contexts else {'path': str(args.contexts), 'sha256': sha(args.contexts.read_bytes())},
        'verifier_sha256': sha(Path(__file__).read_bytes())}
    payload = (json.dumps(report, indent=2, ensure_ascii=False) + '\n').encode()
    if args.receipt.exists():
        require(args.receipt.read_bytes() == payload, 'Receipt frozen: choose an explicit new receipt name for changed public context')
    else:
        args.receipt.write_bytes(payload)
    print(json.dumps({'status': report['status'], 'parents': 7, 'clauses': 14,
        'actual_typed_witnesses_confirmed': False, 'receipt': str(args.receipt), 'sha256': sha(payload)}))


if __name__ == '__main__':
    main()
