"""Preserve raw captures and compare every mathematical root with the frozen tool.

Only the sixty actual, typed compiler front-end definitions may receive
source-generation classification. Their whole bodies remain in the raw audit.
This script performs no Expr, Name, binder, number, or proof normalization.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess
import sys

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
COMPARATOR = ROOT / 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
COMPARATOR_SHA = '28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
CONFIG = json.loads((A / 'notation-frontend-owners-plan.json').read_text())
OWNERS = {x['short']: x['notation_clauses'] for x in CONFIG['owners']}
SHORTS = list(OWNERS)
GENERATED = sum(n * 3 for n in OWNERS.values())
assert GENERATED == CONFIG['expected_public_frontend_definitions'] == 60
TYPES = {'Lean.ParserDescr', 'Lean.Macro', 'Lean.PrettyPrinter.Unexpander'}


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for part in iter(lambda: f.read(1024 * 1024), b''):
            h.update(part)
    return h.hexdigest()


def name_text(tree):
    if tree == ['anonymous']:
        return ''
    assert tree[0] in ('str', 'num') and len(tree) == 3
    prefix = name_text(tree[1])
    return (prefix + '.' if prefix else '') + str(tree[2])


def inventory(witness, short, side):
    old = 'TranscendentalNakamaye.Pending.' + short
    new = 'Hironaka.Resolution.' + short
    owner = old if side == 'original' else new
    rows = [r for r in witness['actual_original_and_public_parser_roots']
            if r['actual_module_owner'] == owner]
    assert len(rows) == 3 * OWNERS[short]
    assert all(sum(r['actual_type'] == t for r in rows) == OWNERS[short] for t in TYPES)
    result = {}
    for row in rows:
        assert row['kind'] == 'definition' and row['whole_value_present'] is True
        name = row['actual_name']
        if side == 'original':
            old_prefix = '_private.' + old + '.0.' + old + '.'
            assert name.startswith(old_prefix), name
            # The frozen capture already applies its namespace/owner map.
            # This identifies that unchanged record; it never rewrites a DAG.
            name = '_private.' + new + '.0.Hironaka.' + short + '.' + name[len(old_prefix):]
        assert name not in result
        result[name] = row
    return result


def capture(status, witness, side, out):
    parser = []
    keys = set()
    all_count = math_count = 0
    frozen_inputs = []
    with (out / (side + '-all.jsonl')).open('w') as all_out, \
            (out / (side + '-mathematical.jsonl')).open('w') as math_out, \
            (out / (side + '-typed-parser.jsonl')).open('w') as parser_out:
        for short in SHORTS:
            module = 'Hironaka.Resolution.' + short
            rec = status['modules'][module]
            assert rec['capture_exit'] == 0 and rec['transport_errors'] == []
            assert rec['public_roots_filtered'] == 0
            assert rec['original_parent_rows_modified'] is False
            for item in rec['frozen_inputs']:
                assert sha(Path(item['path'])) == item['sha256'], item['path']
            source = ROOT / rec['captures'][side + '-unfiltered']['path']
            assert sha(source) == rec['captures'][side + '-unfiltered']['gzip_sha256']
            frozen_inputs.append({'path': str(source), 'sha256': sha(source),
                                  'capture_folder': rec['folder']})
            names = inventory(witness, short, side)
            seen_parser = set()
            seen_names = set()
            row_count = byte_count = theorem_count = 0
            raw_hash = hashlib.sha256()
            with gzip.open(source, 'rt') as stream:
                for line in stream:
                    raw_hash.update(line.encode())
                    byte_count += len(line.encode())
                    row_count += 1
                    r = json.loads(line)
                    seen_names.add(r['name'])
                    theorem_count += r['kind'] == 'theorem'
                    key = (r['module'], r['name'])
                    assert key not in keys
                    keys.add(key)
                    assert r['module'] == module
                    all_out.write(line)
                    all_count += 1
                    if r['name'] in names:
                        w = names[r['name']]
                        node = r['fullExprNodes'][r['typeRoot']]
                        assert r['kind'] == 'definition' and r['valueRoot'] is not None
                        assert node['tag'] == 'constant' and node['children'] == []
                        assert name_text(node['data'][0]) == w['actual_type']
                        assert node['data'][1] == []
                        parser_out.write(line)
                        seen_parser.add(r['name'])
                        parser.append({'module': module, 'name': r['name'],
                                       'type': w['actual_type'],
                                       'raw_record_sha256': hashlib.sha256(line.encode()).hexdigest()})
                    else:
                        math_out.write(line)
                        math_count += 1
            assert raw_hash.hexdigest() == rec['captures'][side + '-unfiltered']['uncompressed_sha256']
            declared = rec['captures'][side + '-unfiltered']
            assert row_count == declared['actual_roots']
            assert byte_count == declared['uncompressed_bytes']
            assert seen_names == set(declared['actual_root_names'])
            assert theorem_count == declared['whole_theorem_proofs']
            assert seen_parser == set(names)
    assert len(parser) == GENERATED and all_count == math_count + GENERATED
    return {'all': all_count, 'mathematical': math_count, 'parser': parser,
            'frozen_lossless_captures': frozen_inputs}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('attempt', help='New immutable output directory name')
    p.add_argument('--witness', default='all-notation-logical-isolation.json')
    args = p.parse_args()
    out = A / args.attempt
    assert not out.exists()
    assert sha(COMPARATOR) == COMPARATOR_SHA
    witness_path = A / args.witness
    witness = json.loads(witness_path.read_text())
    run = witness_path.parent
    verification_path = run / 'verification.json'
    verification = json.loads(verification_path.read_text())
    assert verification['status'] == 'PASS' and verification['exit'] == 0
    assert verification['source_inputs_unchanged'] is True
    assert verification['native_and_control_inputs_unchanged'] is True
    assert verification['no_warning_or_error_diagnostics'] is True
    assert verification['single_fair_reader'] is True
    assert verification['public_artifacts_protected_by_shared_build_lock'] is True
    assert (run / 'probe.exit').read_text().strip() == '0'
    for name, digest in verification['evidence_sha256'].items():
        assert sha(run / name) == digest, name
    assert verification['evidence_sha256'][witness_path.name] == sha(witness_path)
    source_inputs = json.loads((run / 'source-inputs.json').read_text())
    current_sources = {str(x.relative_to(ROOT)) for x in
                       [ROOT / 'Hironaka.lean', *(ROOT / 'Hironaka').rglob('*.lean')]}
    assert current_sources == set(source_inputs)
    for name, digest in source_inputs.items():
        assert sha(ROOT / name) == digest, name
    for inventory_name in ['native-inputs.json', 'public-artifacts.json', 'control-inputs.json']:
        for name, digest in json.loads((run / inventory_name).read_text()).items():
            assert sha(Path(name)) == digest, name
    assert (run / 'notation-plan.json').read_bytes() == (A / 'notation-frontend-owners-plan.json').read_bytes()
    node_plan_path = A / 'blueprint-original-node-extract-plan.json'
    assert (run / 'node-extract-plan.json').read_bytes() == node_plan_path.read_bytes()
    node_plan = json.loads(node_plan_path.read_text())
    upstream_only = sorted({name for spec in node_plan['extracts'].values()
                            for name in spec['separately_verified_original_bindings']})
    assert len(upstream_only) == CONFIG['expected_upstream_only_names'] == 17
    assert witness['actual_upstream_only_public_names_verified_absent'] == upstream_only
    assert witness['status'] == 'PASS_ACTUAL_COMPILER_TYPES_AND_NO_LOGICAL_CONSTANT_DEPENDENTS'
    assert len(witness['actual_original_and_public_parser_roots']) == 2 * GENERATED
    assert witness['direct_references_to_public_parser_roots'] == []
    assert witness['all_public_moduleData_modules'] == len(list((ROOT / 'Hironaka').rglob('*.lean'))) + 1
    assert witness['parser_body_structural_equality_claimed'] is False
    assert witness['roots_excluded_from_kernel_or_axiom_inventory'] == 0
    assert witness['actual_new_moduleData_modules'] == CONFIG['expected_new_physical_modules']
    status_path = A / 'final-per-module-expressions/status.json'
    status = json.loads(status_path.read_text())
    out.mkdir()
    (out / 'status-input-snapshot.json').write_bytes(status_path.read_bytes())
    (out / 'classifier.py.txt').write_bytes(Path(__file__).read_bytes())
    (out / 'notation-plan.json').write_bytes((A / 'notation-frontend-owners-plan.json').read_bytes())
    sides = {s: capture(status, witness, s, out) for s in ['original', 'public']}
    assert sides['original']['all'] == sides['public']['all']
    raw_report = out / 'raw-all-ten-parents-comparison.json'
    math_report = out / 'strict-all-mathematical-roots-comparison.json'
    with (out / 'raw-comparison.log').open('w') as log:
        raw = subprocess.run([sys.executable, str(COMPARATOR), str(out / 'original-all.jsonl'),
                              str(out / 'public-all.jsonl'), str(raw_report)], stdout=log, stderr=subprocess.STDOUT)
    assert raw.returncode == 1
    blocked = json.loads(raw_report.read_text())
    assert blocked['status'] == 'BLOCKED_EXACT_DIFFERENCE'
    old_keys = {(r['module'], r['name']) for r in sides['original']['parser']}
    new_keys = {(r['module'], r['name']) for r in sides['public']['parser']}
    confined = (all(tuple(k) in old_keys for k in blocked['missing']) and
                all(tuple(k) in new_keys for k in blocked['native_extras']) and
                all(tuple(r['constant']) in old_keys | new_keys for r in blocked['differences']))
    with (out / 'mathematical-comparison.log').open('w') as log:
        math = subprocess.run([sys.executable, str(COMPARATOR), str(out / 'original-mathematical.jsonl'),
                               str(out / 'public-mathematical.jsonl'), str(math_report)], stdout=log, stderr=subprocess.STDOUT)
    result = {'status': 'PASS_ALL_MATHEMATICAL_ROOTS_STRICT_WITH_SIXTY_DISCLOSED_FRONTEND_DEFINITIONS'
              if confined and math.returncode == 0 else 'BLOCKED_MATHEMATICAL_EXPRESSION_DIFFERENCE',
              'sides': sides, 'raw_all_actual_status': blocked['status'],
              'raw_differences_confined_to_typed_frontend_definitions': confined,
              'mathematical_comparison_exit': math.returncode,
              'typed_whole_environment_witness': {'path': str(witness_path), 'sha256': sha(witness_path)},
              'typed_witness_runner_verification': {'path': str(verification_path),
                                                    'sha256': sha(verification_path)},
              'separate_source_generation_and_all_actual_axiom_kernel_gates_required': True,
              'parser_body_structural_equality_claimed': False,
              'raw_Expr_Name_number_binder_or_proof_normalization': False,
              'comparator_sha256': sha(COMPARATOR)}
    (out / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], 'actual roots', sides['public']['all'],
          'strict mathematical roots', sides['public']['mathematical'], flush=True)
    return 0 if confined and math.returncode == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
