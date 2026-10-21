"""Bounded read-only source-generation evidence; never a whole-Expr PASS.

Adapt the established 20261015 parser source-generation protocol to exactly
three complete original parents and their eighteen original generated outputs.
Supersedes the historical receipt after FOUR further authentic PrincipalJet
declaration-local contexts; preserves every historical receipt and verifier.
Read ordinary Git source, replay ONLY the frozen namespace/import relocation
and explicitly recorded administrative contexts, and check whole public bytes.
No Lean process, Expr export/comparison, production write, or normalization.
"""
from pathlib import Path
import argparse
import ast
from collections import Counter
import hashlib
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
A = HERE.parents[1]
ROOT = A.parents[1]
SOURCE = Path('/workspace/archon-publish')
REVISION = '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
ACCEPTED = '82934a028fb2c94d5a706bf66343fd4614e8a884'
COMPARATOR = ROOT / 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
COMPARATOR_SHA = '28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
PROTOCOL = ROOT / 'audit/analytic-coefficient-dictionary-and-chosen-overlaps-20261015/verify_final_parser_source_generation.py'
RELOCATION = ROOT / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
HEADER = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
SOURCE_HASHES = {
    'HironakaActualClosedContactControlledRestriction': 'e1cfacd54c222a726bfef394c9871d7b36eeac6cb6f0f1e8944082aaa5922cc3',
    'HironakaActualPrincipalJetMultiplication': '188aed6b5048d754a7d4bbe74175db5524f08732894aa4674328e80ea9a30f09',
    'HironakaActualPrincipalHSFormula': 'f09b3cf9efc949dc422e86bc1cf86a53ae2a4ffa342d4d9f524a5483a51c4a42',
}
NOTATIONS = {
    'HironakaActualClosedContactControlledRestriction': [
        'local notation "S" => geoStrictTransform π ((Subtype.val : N → A) \'\' D) N',
        'local notation "σ" => restrictedProjection hNc D hπ'],
    'HironakaActualPrincipalJetMultiplication': [
        'local notation "R" => HolGerm (ComplexModel n)',
        'local notation "𝔪" => IsLocalRing.maximalIdeal R'],
    'HironakaActualPrincipalHSFormula': [
        'local notation "R" => HolGerm (ComplexModel n)',
        'local notation "𝔪" => IsLocalRing.maximalIdeal R'],
}
ZERO_BEFORE = '/-- A nonzero ORIGINAL germ alone supplies the entire existing principal HS profile. -/\n'
ZERO_CONTEXT = {'before': ZERO_BEFORE, 'after':
    'attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in\n' + ZERO_BEFORE}


JET_BEFORES = [
    '/-- The actual Noetherian local ring has no nonzero germ in every positive maximal power. -/',
    '/-- The least genuine failed original maximal power, chosen from the original nonzero germ. -/',
    '/-- Both actual original order conditions are produced, including order zero for units. -/',
    '/-- The genuine two-sided maximal-power conditions determine the original order uniquely. -/',
]
JET_CONTEXTS = [{'before': before, 'after':
    'attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in\n' + before}
    for before in JET_BEFORES]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def exact_notation_context(text):
    lines = text.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith('local notation ')]
    require(len(indices) == 2, 'Expected exactly two original local notations')
    first, last = indices
    start = max(i for i in range(first) if lines[i].startswith('variable '))
    return ''.join(lines[start:last + 1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', choices=['preliminary', 'final'], required=True)
    args = parser.parse_args()
    require(subprocess.check_output(['git', '-C', str(SOURCE), 'rev-parse', REVISION],
                                    text=True).strip() == REVISION, 'Changed ordinary Git revision')
    require(sha(COMPARATOR.read_bytes()) == COMPARATOR_SHA, 'Frozen comparator changed')
    sys.path.insert(0, str(ROOT / 'scripts'))
    import upstream_namespace_map as names
    names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'
                           for s in ['', '2', '3', '4']])
    flat = names.flattened_short()
    fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'
                    + '|'.join(flat) + r')\.(?=[\w«])')
    function = next(n for n in ast.parse(RELOCATION.read_text()).body
                    if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
    scope = {'names': names, 'fq': fq, 're': re, 'flat': flat}
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(RELOCATION), 'exec'), scope)
    ancestry_path = HERE / 'six-new-parent-original-context-scope-map.json'
    ancestry = read_json(ancestry_path)
    matching_scope = [s for s in ancestry['scopes'] if s['declaration_scope'] ==
        'Hironaka.HironakaActualPrincipalHSFormula.hilbertSamuelValue_actual_principal_order']
    require(len(matching_scope) == 1 and matching_scope[0]['exact_insertion_anchor'] == ZERO_BEFORE and
            matching_scope[0]['context_candidates'] ==
            ['attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in'] and
            ancestry['zero_original'] == ['ZeroMemClass.zero', 'AddSubmonoidClass.toZeroMemClass',
                'SubsemiringClass.toAddSubmonoidClass', 'SubringClass.toSubsemiringClass'],
            'Missing exact compiled-original class-ancestor context evidence')
    records = read_json(A / 'provenance.json')
    witness_path = A / 'three-native-notation-owner-witness.json'
    witness_log = A / 'three-native-notation-owner-witness.log'
    witnesses = read_json(witness_path)
    require(len(witnesses) == 18, 'Missing original eighteen actual typed witnesses')
    require(witness_log.read_text() == 'ACTUAL_THREE_NATIVE_NOTATION_OWNERS 18; no public classification or structural-equality claim\n',
            'Missing successful original witness completion log')
    require(len({w['actual_name'] for w in witnesses}) == 18, 'Duplicate actual original generated name')
    parents = []
    for stem, frozen_sha in SOURCE_HASHES.items():
        original_owner = 'TranscendentalNakamaye.Pending.' + stem
        public_owner = 'Hironaka.Resolution.' + stem
        selected = [r for r in records if r['source_module'] == original_owner]
        require(len(selected) == 1, 'Nonunique whole original provenance: ' + stem)
        rec = selected[0]
        require(rec['accepted_checkpoint'] == ACCEPTED and
                rec['published_source_revision'] == REVISION and
                rec['destination_module'] == public_owner and
                rec['original_proof_tokens_changed'] is False, 'Changed source identity: ' + stem)
        raw = subprocess.check_output(['git', '-C', str(SOURCE), 'show', REVISION + ':' + rec['source_path']])
        require(sha(raw) == rec['source_sha256'] == frozen_sha, 'Changed whole original source: ' + stem)
        original = raw.decode()
        initial = HEADER + scope['relocate'](original)
        require(sha(initial.encode()) == rec['initial_synchronized_destination_sha256'],
                'Whole canonical relocation replay failed: ' + stem)
        contexts = rec['administrative_elaboration_contexts']
        allowed = ([ZERO_CONTEXT] if stem == 'HironakaActualPrincipalHSFormula' else
                   JET_CONTEXTS if stem == 'HironakaActualPrincipalJetMultiplication' else [])
        require(contexts in [[], allowed], 'Unreviewed source administrative edit: ' + stem)
        if args.stage == 'final':
            require(contexts == allowed, 'Final genuine theorem context has not been applied: ' + stem)
        expected = initial
        for edit in contexts:
            require(expected.count(edit['before']) == 1, 'Nonunique original context anchor: ' + stem)
            require(expected.index(edit['before']) > expected.rindex('local notation '),
                    'Administrative theorem edit touches notation context: ' + stem)
            expected = expected.replace(edit['before'], edit['after'])
        extras = rec['additional_pure_support_imports']
        require(extras == [], 'Unexpected extra imports in these three notation parents')
        public = (ROOT / rec['destination_path']).read_bytes()
        require(expected.encode() == public and sha(public) == rec['destination_sha256'],
                'Complete public source differs from exact administrative replay: ' + stem)
        original_notations = [line for line in original.splitlines() if line.startswith('local notation ')]
        public_notations = [line for line in public.decode().splitlines() if line.startswith('local notation ')]
        require(original_notations == public_notations == NOTATIONS[stem], 'Notation text changed: ' + stem)
        context = exact_notation_context(original)
        require(context == exact_notation_context(public.decode()), 'Notation variable/include context changed: ' + stem)
        owned = [w for w in witnesses if w['actual_owner'] == original_owner]
        require(len(owned) == 6 and Counter(w['actual_type'] for w in owned) == Counter({
            'Lean.ParserDescr': 2, 'Lean.Macro': 2, 'Lean.PrettyPrinter.Unexpander': 2}),
            'Wrong actual original generated-type inventory: ' + stem)
        require(all(w['kind'] == 'definition' and w['whole_value_present'] is True for w in owned),
                'Missing complete actual original generated definition: ' + stem)
        parents.append({'whole_source_record': rec, 'original_source_bytes': len(raw),
            'public_source_bytes': len(public), 'whole_source_replay_exact': True,
            'same_literal_local_notations': original_notations,
            'same_literal_variable_include_context': context,
            'same_literal_variable_include_context_sha256': sha(context.encode()),
            'genuine_context_applied_only_after_notations': contexts,
            'six_actual_original_generated_outputs': owned})
    report = {'status': 'PASS_BOUNDED_WHOLE_SOURCE_GENERATION_EVIDENCE_AFTER04_' + args.stage.upper(),
        'original_ordinary_git_checkout': str(SOURCE), 'original_ordinary_git_revision': REVISION,
        'accepted_native_checkpoint': ACCEPTED, 'complete_original_public_parents_checked': 3,
        'actual_original_frontend_definitions': 18, 'parents': parents,
        'all_three_sources_verified_against_full_ordinary_git_blobs': True,
        'same_local_notation_and_variable_contexts': True,
        'genuine_theorem_context_original_ancestor_evidence': matching_scope[0],
        'historical_source_generation_receipt_superseded': 'three-notation-source-generation-final.json',
        'four_PrincipalJet_contexts_after_unchanged_notations': JET_CONTEXTS,
        'context_ancestor_diagnosis_is_not_a_claim_of_recompiled_proof_equality': True,
        'replay_rule': 'Frozen existing relocate function, original complete source, release header, explicitly recorded theorem-local context only.',
        'public_18_typed_witness_gate_claimed_here': False,
        'actual_whole_environment_no_dependents_gate_claimed_here': False,
        'whole_parser_body_structural_equality_claimed_here': False,
        'whole_mathematical_root_structural_equality_claimed_here': False,
        'final_kernel_or_axiom_pass_claimed_here': False,
        'roots_excluded_or_normalized': 0, 'proof_type_payload_edits': 0,
        'source_data_read_only': True, 'lean_processes_or_expr_exports_run': 0,
        'separate_pending_parent_gates': [
            'Final 36 actual original/public generated-output typed owner witnesses.',
            'Actual whole public environment direct type/value dependency scan.',
            'Frozen raw whole-Expr comparison and precise mathematical/frontend classification.',
            'All actual roots remain in complete kernel and axiom inventory.'],
        'frozen_comparator_sha256': COMPARATOR_SHA,
        'evidence_sha256': {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in [
            PROTOCOL, RELOCATION, ROOT / 'scripts/upstream_namespace_map.py',
            ancestry_path, HERE / 'six-new-parent-instance-ancestor-diagnosis.json',
            A / 'support-prep/principal-jet-first-dag-diagnosis.json',
            HERE / 'three-notation-source-generation-final.json',
            HERE / 'verify_three_notation_source_generation.py',
            A / 'provenance.json', A / 'source-replay-receipt.json', witness_path, witness_log]},
        'verifier_sha256': sha(Path(__file__).read_bytes())}
    destination = HERE / ('three-notation-source-generation-after04-' + args.stage + '.json')
    payload = (json.dumps(report, ensure_ascii=False, indent=2) + '\n').encode()
    if args.stage == 'final' and destination.exists():
        require(destination.read_bytes() == payload, 'Final evidence is frozen; explicit parent review needed to refresh')
    else:
        destination.write_bytes(payload)
    print(json.dumps({'status': report['status'], 'parents': 3, 'original_typed_outputs': 18,
                      'report': str(destination), 'report_sha256': sha(payload)}, ensure_ascii=False))


if __name__ == '__main__':
    main()
