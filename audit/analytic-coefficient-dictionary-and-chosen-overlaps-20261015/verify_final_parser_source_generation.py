"""Read-only source/actual-environment evidence for three divergent parser roots.

This does not normalize Names or numbers and does not grant structural equality.
It consumes the actual Lean type/dependency probe already run by the publisher.
The full equality and frozen kernel gates remain separate requirements.
"""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = Path('/workspace/archon-nakamaye-publish')
REVISION = '09dc511c4a14836a0287748d1a63f9f467f677d3'
FROZEN_NATIVE = 'db4e4065403b4ab8b077fac41985825931e5cc02'
OLD = 'TranscendentalNakamaye.Pending.RiemannExtensionThin'
NEW = 'Hironaka.Analytic.RiemannExtensionThin'
COMPARATOR = ROOT / 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
COMPARATOR_SHA = '28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(part)
    return h.hexdigest()


def load(name):
    return json.loads((HERE / name).read_text())


def main():
    recs = [r for r in load('provenance.json') if r['source_module'] == OLD]
    require(len(recs) == 1, 'No unique complete original source provenance')
    rec = recs[0]
    require(rec['source_revision'] == FROZEN_NATIVE and rec['destination_module'] == NEW,
            'Changed original/public source identity')
    require(not rec['administrative_elaboration_contexts'], 'Parser source has an administrative edit')
    require(rec['additional_pure_support_imports'] == ['Hironaka.Support.RiemannBoundedExact'],
            'Unexpected extra source import')
    raw = subprocess.check_output(['git', '-C', str(SOURCE), 'show', REVISION + ':' + rec['source_path']])
    require(sha(raw) == rec['source_sha256'] ==
            'a5405c624b74017fe1a6b861192ba7a05cc3697fe2547e15feb520b02b6a9d9c',
            'Original source does not match both published and frozen provenance')
    # Replay the already-reviewed canonical namespace rule, rather than invent a
    # parser-specific source transformation or re-elaborate a different notation.
    sys.path.insert(0, str(ROOT / 'scripts'))
    import upstream_namespace_map as names
    names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
    flat = names.flattened_short()
    fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
    relocation_source = ROOT / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
    relocation = next(n for n in ast.parse(relocation_source.read_text()).body
                      if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
    scope = {'names': names, 'fq': fq, 're': re, 'flat': flat}
    exec(compile(ast.Module(body=[relocation], type_ignores=[]), str(relocation_source), 'exec'), scope)
    header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
    expected = header + scope['relocate'](raw.decode())
    require(sha(expected.encode()) == rec['initial_synchronized_destination_sha256'],
            'Complete canonical source replay differs')
    first = re.search(r'^import ', expected, re.M)
    require(first is not None, 'Missing original imports')
    expected = expected[:first.start()] + 'import Hironaka.Support.RiemannBoundedExact\n' + expected[first.start():]
    public_path = ROOT / (NEW.replace('.', '/') + '.lean')
    require(expected.encode() == public_path.read_bytes() and
            file_sha(public_path) == rec['destination_sha256'] ==
            '08dd45bfc5b2fa1a34d6caf8438578b17e51cd5f9a729aa3b8b749b456c76517',
            'Whole original/public parser-containing source changed')
    notation = 'local notation "E" => EuclideanSpace ℂ (Fin d)'
    require(raw.decode().splitlines().count(notation) == expected.splitlines().count(notation) == 1,
            'Notation was changed, duplicated, or omitted')
    require('variable {d : ℕ}\n\n' + notation in raw.decode() and
            'variable {d : ℕ}\n\n' + notation in expected, 'Notation variable context changed')

    actual = load('parser-logical-isolation-final.json')
    witness = load('parser-generated-owner-witness.json')
    rows = actual['actual_original_and_public_parser_roots']
    require(actual['status'] == 'PASS_ACTUAL_COMPILER_TYPES_AND_NO_LOGICAL_CONSTANT_DEPENDENTS' and
            len(rows) == len(witness) == 6, 'Missing actual Lean type/dependency evidence')
    expected_types = {'Lean.ParserDescr', 'Lean.Macro', 'Lean.PrettyPrinter.Unexpander'}
    for owner in (OLD, NEW):
        selected = [r for r in rows if r['actual_module_owner'] == owner]
        require(len(selected) == 3 and {r['actual_type'] for r in selected} == expected_types,
                'Expected one actual descriptor, macro, unexpander per module')
        for r in selected:
            require(r['kind'] == 'definition' and r['whole_value_present'] is True,
                    'Missing actual entire generated definition')
            matches = [w for w in witness if w['owner'] == owner and w['name'] == r['actual_name']]
            require(len(matches) == 1 and matches[0]['type'] ==
                    'Lean.Expr.const `' + r['actual_type'] + ' []', 'Actual owner/type witnesses disagree')
    require(actual['all_public_moduleData_modules'] == 969 and
            actual['all_public_moduleData_constants'] == 16571 and
            actual['all_public_moduleData_theorems'] == 13038 and
            actual['other_actual_constants_scanned'] == 16568 and
            actual['direct_type_constant_edges_scanned'] == 605859 and
            actual['direct_entire_value_constant_edges_scanned'] == 1029586 and
            actual['direct_references_to_three_public_parser_roots'] == [] and
            actual['parser_body_structural_equality_claimed'] is False and
            actual['roots_excluded_from_kernel_or_axiom_inventory'] == 0,
            'Actual complete direct-dependency inventory changed or has a reference')
    require((HERE / 'parser-logical-isolation-final.log').read_text().strip() ==
            'PARSER_LOGICAL_ISOLATION modules=969 constants=16571 other=16568 references=0',
            'Missing actual successful dependency-probe run')
    require((HERE / 'parser-generated-owner-witness-03.log').read_text().strip() ==
            'ACTUAL_PARSER_GENERATED_OWNER_WITNESSES 6', 'Missing actual successful owner probe')
    roots = {r['actual_name'] for r in rows if r['actual_module_owner'] == NEW}
    snapshots = {}
    # Preserve original whole ASTs. This is selection for source-generation
    # evidence only; no root is removed from the full raw comparison/inventory.
    for name in ('native-full-expressions.jsonl',
                 'public-full-expressions-final.jsonl'):
        selected = []
        total = 0
        for line in (HERE / name).open():
            total += 1
            r = json.loads(line)
            if r['module'] == NEW and r['kind'] == 'definition':
                require(r['valueRoot'] is not None, 'Missing full actual parser value')
                selected.append({'actual_exported_name': r['name'],
                    'whole_record_sha256': sha(line.encode()), 'nodes': len(r['fullExprNodes']),
                    'typeRoot': r['typeRoot'], 'valueRoot': r['valueRoot']})
        require(total == 924 and len(selected) == 3, 'Raw entire snapshot inventory changed')
        if name.startswith('public-'):
            require({r['actual_exported_name'] for r in selected} == roots, 'Actual public roots changed')
        snapshots[name] = {'sha256': file_sha(HERE / name), 'all_actual_roots': total,
                           'three_complete_raw_parser_records': selected}
    raw_report = load('all-actual-raw-structural-comparison-final.json')
    require(raw_report['status'] == 'BLOCKED_EXACT_DIFFERENCE', 'Original strict raw failure was hidden')
    require(file_sha(COMPARATOR) == COMPARATOR_SHA, 'Frozen comparator changed')
    require(NEW in load('kernel-modules.json'), 'Parser-containing module omitted from kernel targets')
    actual_log = (HERE / 'public-all-actual-compiled-roots-after-prerequisite-repair.log').read_text()
    require('ALL_LIBRARY_MODULES 969' in actual_log and 'NEW_ACTUAL_ROOTS 1009' in actual_log and
            'MISSING 0' in actual_log and 'STANDARD_THREE_ONLY' in actual_log,
            'Missing all-actual compiled/axiom success evidence')
    pinned = ['ParserLogicalIsolationFinal.lean', 'parser-logical-isolation-final.json',
              'parser-logical-isolation-final.log', 'ParserGeneratedOwnerWitness.lean',
              'parser-generated-owner-witness.json', 'parser-generated-owner-witness-03.log',
              'public-all-actual-compiled-roots-after-prerequisite-repair.log', 'kernel-modules.json',
              'all-actual-raw-structural-comparison-final.json']
    report = {'status': 'PASS_REFRESHED_TYPED_SOURCE_GENERATION_GATE_WITH_INDEPENDENT_INITIAL_REVIEW',
        'original_frozen_revision': FROZEN_NATIVE, 'normal_published_revision': REVISION,
        'whole_source_record': rec, 'exact_unchanged_local_notation': notation,
        'actual_original_and_public_parser_definitions': rows,
        'all_owned_actual_constants': 16571, 'other_actual_constants_scanned': 16568,
        'direct_type_edges': 605859, 'direct_whole_value_edges': 1029586,
        'direct_references_to_three_parser_roots': 0,
        'preserved_complete_raw_snapshots': snapshots,
        'whole_other_roots_equality_claimed_here': False,
        'three_parser_bodies_equality_claimed': False,
        'numbers_alpha_defeq_normalized': False,
        'raw_all_root_strict_status': 'BLOCKED_EXACT_DIFFERENCE',
        'all_actual_axiom_probe_includes_parser_module': True,
        'parser_module_recorded_in_fresh_kernel_targets': True,
        'final_frozen_kernel_PASS_claimed_here': False,
        'publication_requirements': [
            'Every other actual new root must have complete type/value structural equality (expected 1006 of 1009).',
            'All 1009 actual roots remain captured and covered by standard-axiom and frozen kernel inventory.',
            'Final publication must retain raw all-root BLOCKED and disclose precisely three generated front-end outputs as divergent.',
            'No numerical/alpha/defeq normalization, proof omission, or all-1009 strict-PASS wording.'],
        'evidence_sha256': {f: file_sha(HERE / f) for f in pinned},
        'verifier_sha256': file_sha(Path(__file__)), 'frozen_comparator_sha256': COMPARATOR_SHA}
    target = HERE / 'parser-typed-source-generation-final.json'
    target.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'all_owned_actual_constants',
        'other_actual_constants_scanned', 'direct_references_to_three_parser_roots',
        'raw_all_root_strict_status', 'verifier_sha256')}, ensure_ascii=False))


if __name__ == '__main__':
    main()
