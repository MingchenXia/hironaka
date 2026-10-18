"""Classify ALL actual roots, retaining the three divergent parser definitions.

The unchanged strict comparator checks every other complete mathematical
type/value, including private and generated mathematical helpers. The raw
all-root report remains BLOCKED on the disclosed compiler front-end outputs.
No Name, number, binder, proof or metadata field is normalized here.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
COMPARATOR = ROOT / 'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
assert hashlib.sha256(COMPARATOR.read_bytes()).hexdigest() == '28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
OLD = 'TranscendentalNakamaye.Pending.RiemannExtensionThin'
NEW = 'Hironaka.Analytic.RiemannExtensionThin'
WITNESS = json.loads((HERE / 'parser-logical-isolation.json').read_text())
TYPES = {'Lean.ParserDescr', 'Lean.Macro', 'Lean.PrettyPrinter.Unexpander'}


def name_text(tree):
    if tree == ['anonymous']:
        return ''
    assert tree[0] in ('str', 'num') and len(tree) == 3
    prefix = name_text(tree[1])
    return (prefix + '.' if prefix else '') + str(tree[2])


def parser_inventory(owner):
    rows = [row for row in WITNESS['actual_original_and_public_parser_roots']
            if row['actual_module_owner'] == owner]
    assert len(rows) == 3 and {row['actual_type'] for row in rows} == TYPES
    result = {}
    for row in rows:
        name = row['actual_name']
        if owner == OLD:
            original_prefix = '_private.' + OLD + '.0.' + OLD + '.'
            assert name.startswith(original_prefix)
            # Classify a record under the existing namespace relocation. This
            # does not change a byte in any captured record or its AST.
            name = '_private.' + NEW + '.0.Hironaka.RiemannExtensionThin.' + name[len(original_prefix):]
        assert name not in result
        result[name] = row
    return result


def capture(side, owner, whole, fragment):
    parser_names = parser_inventory(owner)
    all_path = HERE / (side + '-all-actual-full-expressions-final.jsonl')
    math_path = HERE / (side + '-all-mathematical-full-expressions-final.jsonl')
    parser_path = HERE / (side + '-three-parser-full-expressions-final.jsonl')
    counts = {'whole': 0, 'support': 0, 'mathematical': 0, 'parser': 0}
    seen = set()
    parser_records = []
    with all_path.open('w') as all_out, math_path.open('w') as math_out, parser_path.open('w') as parser_out:
        for kind, path in [('whole', whole), ('support', fragment)]:
            for line in (HERE / path).open():
                record = json.loads(line)
                key = (record['module'], record['name'])
                assert key not in seen
                seen.add(key)
                counts[kind] += 1
                all_out.write(line)
                if record['module'] == NEW and record['name'] in parser_names:
                    witness = parser_names[record['name']]
                    type_node = record['fullExprNodes'][record['typeRoot']]
                    assert record['kind'] == 'definition' and record['valueRoot'] is not None
                    assert type_node['tag'] == 'constant' and type_node['children'] == []
                    assert name_text(type_node['data'][0]) == witness['actual_type']
                    assert type_node['data'][1] == []
                    parser_out.write(line)
                    parser_records.append({'module': record['module'], 'name': record['name'],
                        'type': witness['actual_type'], 'complete_raw_record_sha256': hashlib.sha256(line.encode()).hexdigest()})
                    counts['parser'] += 1
                else:
                    math_out.write(line)
                    counts['mathematical'] += 1
    assert counts == {'whole': 924, 'support': 85, 'mathematical': 1006, 'parser': 3}
    assert {row['name'] for row in parser_records} == set(parser_names)
    return all_path, math_path, parser_records


old_all, old_math, old_parser = capture('native', OLD, 'native-full-expressions.jsonl', 'fragment-native-full-expressions.jsonl')
new_all, new_math, new_parser = capture('public', NEW, 'public-full-expressions-final.jsonl', 'fragment-public-full-expressions-final.jsonl')
raw_report = HERE / 'all-actual-raw-structural-comparison-final.json'
math_report = HERE / 'all-mathematical-strict-comparison-final.json'
raw = subprocess.run([sys.executable, str(COMPARATOR), str(old_all), str(new_all), str(raw_report)], cwd=ROOT)
assert raw.returncode == 1
raw_data = json.loads(raw_report.read_text())
assert raw_data['status'] == 'BLOCKED_EXACT_DIFFERENCE'
assert raw_data['missing'] or raw_data['native_extras'] or raw_data['differences']
old_keys = {(row['module'], row['name']) for row in old_parser}
new_keys = {(row['module'], row['name']) for row in new_parser}
assert all(tuple(key) in old_keys for key in raw_data['missing'])
assert all(tuple(key) in new_keys for key in raw_data['native_extras'])
assert all(tuple(row['constant']) in old_keys | new_keys for row in raw_data['differences'])
subprocess.run([sys.executable, str(COMPARATOR), str(old_math), str(new_math), str(math_report)], cwd=ROOT, check=True)
exact = json.loads(math_report.read_text())
assert exact['status'] == 'EXACT_ALL_FULL_EXPR_DAG_MATCH'
assert exact['old']['all_actual_constants'] == exact['native']['all_actual_constants'] == 1006
report = {'status': 'PASS_ALL_1006_MATHEMATICAL_ROOTS_STRICT_WITH_THREE_DISCLOSED_PARSER_SOURCE_AUDITS',
    'total_actual_new_roots_per_side': 1009, 'strict_complete_type_and_value_roots_per_side': 1006,
    'mathematical_theorem_proofs_strict_exact': sum(row['theorem_proofs_exact'] for row in exact['module_counts'].values()),
    'three_original_parser_records': old_parser, 'three_public_parser_records': new_parser,
    'raw_all_actual_structural_status': 'BLOCKED_EXACT_DIFFERENCE',
    'all_raw_differences_confined_to_precisely_disclosed_three_front_end_outputs': True,
    'raw_all_actual_report': raw_report.name, 'strict_mathematical_report': math_report.name,
    'three_parser_bodies_structural_equality_claimed': False,
    'typed_source_generation_independent_receipt': 'g3-parser-typed-source-generation-review.json',
    'normalization_or_proof_editing_in_this_classifier': False,
    'all_actual_roots_captured_losslessly': True,
    'all_actual_axiom_and_frozen_kernel_gates_required_separately': True,
    'classifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE / 'all-actual-root-verification-classification-final.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
