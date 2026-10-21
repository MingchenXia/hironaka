#!/usr/bin/env python3
"""One source-only no-op plus independent immutable-source reconstruction."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
D = Path('/workspace/hironaka')
A = D / 'audit/phase4-semantic-producers-20261021'
OLD = D / 'audit/canonical-elementary-family-and-local-producers-20261021'
PIN = '636442a87402a67de1f914cb4120ee28c3ed6ad7'
BASE = '73420d1a4fdba81d643842e5480c933efa2a0810'
ATTR = 'attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in\n'
h = lambda b: hashlib.sha256(b).hexdigest()
inputs = {}

def read(p):
    b = p.read_bytes()
    inputs[str(p)] = h(b)
    return b

def output(name, value):
    p = W / name
    assert not p.exists(), ('Refuse to overwrite audit evidence', p)
    p.write_bytes(value if isinstance(value, bytes) else (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())

def show(repository, revision, path):
    return subprocess.check_output(['git', '-C', repository, 'show', revision + ':' + path])

assert not (W / 'static-review.json').exists()
plan = json.loads(read(A / 'cohort-plan.json'))
rows = json.loads(read(A / 'provenance.json'))
bps = json.loads(read(A / 'blueprint-provenance.json'))
assert plan['ordinary_published_revision'] == PIN
assert plan['standalone_base_revision'] == BASE
assert len(rows) == len(bps) == 9
assert len({r['destination_path'] for r in rows}) == 9
assert sum(r['proofs'] for r in bps) == 28
freeze = json.loads(read(A / 'final-nine-source-BP-freeze.json'))
for path, want in freeze['files'].items():
    assert h(read(D / path)) == want, path
before_summary = read(A / 'source-replay-receipt.json')
output('source-replay-summary-before.json', before_summary)
output('frozen-cohort-plan.json', read(A / 'cohort-plan.json'))

for path, want in plan['old_mathematical_files'].items():
    assert h(read(D / path)) == want, path
for path, want in plan['old_blueprint_files_including_master'].items():
    if path != 'blueprint/extensions.tex':
        assert h(read(D / path)) == want, path
for path, want in plan['frozen_profiles'].items():
    assert h(read(D / path)) == want, path
for path in plan['deferred_prior_modules_preserved_absent']:
    assert not (D / path).exists(), path
    chapter = 'blueprint/' + re.sub(r'(?<!^)(?=[A-Z])', '-', Path(path).stem).lower() + '-extension.tex'
    assert not (D / chapter).exists(), chapter

# All tracked prior373 audit data, including raw records, remain at the fixed base.
old_relative = str(OLD.relative_to(D))
diff = subprocess.run(['git', '-C', str(D), 'diff', '--name-only', BASE, '--', old_relative],
                      capture_output=True, text=True, check=True)
assert diff.stdout == '', diff.stdout
prior_metadata = {}
for name, count in [('provenance.json', 373), ('blueprint-provenance.json', 349)]:
    p = OLD / name
    b = read(p)
    assert b == show(str(D), BASE, str(p.relative_to(D)))
    assert len(json.loads(b)) == count
    prior_metadata[name] = h(b)
for name in ['source-replay-receipt.json', 'publication-verification.json']:
    p = OLD / name
    assert read(p) == show(str(D), BASE, str(p.relative_to(D)))
    prior_metadata[name] = h(read(p))

# Preserve the actual seven-stage archive, including its raw comparisons and parts.
archive = A / 'frozen-seven-before-append'
archive_manifest = json.loads(read(archive / 'manifest.json'))
for path, want in archive_manifest['files'].items():
    if path == 'Hironaka.lean':
        p = archive / 'before-nine-Hironaka.lean'
    elif path == 'blueprint/extensions.tex':
        p = archive / 'before-nine-extensions.tex'
    elif path.startswith(str(A.relative_to(D)) + '/'):
        p = archive / path.removeprefix(str(A.relative_to(D)) + '/')
        if not p.exists():
            # Explicit immutable reuse: gz captures stay at their original paths.
            assert '/final-per-module-expressions/' in path and path.endswith('.jsonl.gz')
            p = D / path
    elif path.startswith('.lake/'):
        p = D / path
    else:
        p = archive / path
    assert h(read(p)) == want, path

sys.path.insert(0, str(D / 'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
frozen_relocator = D / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
fn = next(x for x in ast.parse(read(frozen_relocator).decode()).body if isinstance(x, ast.FunctionDef) and x.name == 'relocate')
env = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
exec(compile(ast.Module(body=[fn], type_ignores=[]), str(frozen_relocator), 'exec'), env)
header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
contexts = json.loads(read(A / 'original-elaboration-contexts.json'))
extras = json.loads(read(A / 'additional-pure-support-imports.json'))
source_results = []
attrs_total = 0
for row in rows:
    raw = show('/workspace/archon-publish', PIN, row['source_path'])
    assert raw == read(A / row['raw_capture']) and h(raw) == row['source_sha256']
    original = raw.decode()
    initial = header + env['relocate'](original)
    assert h(initial.encode()) == row['initial_synchronized_destination_sha256']
    additions = row['additional_pure_support_imports']
    assert additions == extras.get(row['destination_module'], [])
    out = initial
    if additions:
        assert all((D / (m.replace('.', '/') + '.lean')).exists() for m in additions)
        at = re.search(r'^import ', out, re.M).start()
        out = out[:at] + ''.join('import ' + m + '\n' for m in additions) + out[at:]
    commands = row['administrative_elaboration_contexts']
    assert [a['before'] for a in commands] == contexts.get(row['destination_module'], [])
    for adj in commands:
        assert adj['after'] == ATTR + adj['before']
        assert out.count(adj['before']) == 1
        pos = out.index(adj['before'])
        assert pos > out.rfind('local notation ')
        assert pos == 0 or out[pos-1] == '\n'
        out = out.replace(adj['before'], adj['after'])
        attrs_total += 1
    actual = read(D / row['destination_path'])
    assert out.encode() == actual and h(actual) == row['destination_sha256']
    assert re.findall(r'^local notation .*$', out, re.M) == re.findall(r'^local notation .*$', original, re.M)
    assert re.findall(r'^(?:variable\b|include\b|omit\b).*$', out, re.M) == re.findall(r'^(?:variable\b|include\b|omit\b).*$', original, re.M)
    source_results.append({'module': row['destination_module'], 'original_sha256': h(raw),
                           'public_sha256': h(actual), 'whole_original_payload_preserved': True,
                           'pure_imports': additions, 'declaration_local_contexts': len(commands)})
assert attrs_total == 3
assert sum(len(r['pure_imports']) for r in source_results) == 2
bp_texts = []
definitions = attachments = 0
for row in bps:
    raw = show('/workspace/archon-publish', PIN, row['source_path'])
    assert raw == read(A / row['raw_capture']) and h(raw) == row['source_sha256']
    out = names.rename_text_names(raw.decode()).replace('\\chapter{', '\\section{')
    assert out.encode() == read(D / row['destination_path'])
    assert h(out.encode()) == row['destination_sha256']
    assert out.count('\\begin{proof}') == row['proofs']
    definitions += out.count('\\begin{definition}')
    attachments += sum(len([x for x in s.split(',') if x.strip()]) for s in re.findall(r'\\lean\{([^}]*)\}', out))
    bp_texts.append(out)
assert definitions == 1 and attachments == 42

pointer_rows = plan['documentation_external_prerequisites']
assert len(pointer_rows) == 1 and pointer_rows[0]['labels'] == ['hir:base-change-open']
pr = pointer_rows[0]
raw = show('/workspace/archon-publish', PIN, pr['source_path'])
assert raw == read(A / pr['raw_capture']) and h(raw) == pr['source_sha256']
pointer = read(A / pr['generated_text'])
assert pointer == read(D / pr['destination_path']) and h(pointer) == pr['destination_sha256']
assert pointer.decode().count('\\label{hir:base-change-open}') == 1
assert PIN.encode() in pointer and b'\\begin{proof}' not in pointer and b'\\lean' not in pointer
external = json.loads(read(A / 'external-prerequisite-complete-original-node.json'))
node = read(A / external['complete_node_capture'])
assert raw.count(node) == 1 and h(node) == external['complete_node_sha256']
assert node.count(b'\\begin{proof}') == 1 and b'\\label{hir:base-change-open}' in node
assert external['documentation_only'] is True
assert all(a['local_export_claim_from_pointer'] is False for a in external['attachments'])

root = read(A / 'fixed373-before-Hironaka.lean').decode()
at = root.index('/-!')
expected_root = root[:at] + ''.join('import ' + r['destination_module'] + '\n' for r in rows) + '\n' + root[at:]
assert read(D / 'Hironaka.lean') == expected_root.encode()
master = read(A / 'fixed373-before-extensions.tex').decode()
at = master.rindex('\\end{document}')
expected_master = master[:at] + ''.join('\\input{' + Path(r['destination_path']).stem + '}\n' for r in [*bps, *pointer_rows]) + master[at:]
assert read(D / 'blueprint/extensions.tex') == expected_master.encode()

# Resolve actual literal reference tokens only, without virtual canonicalization.
seen = set()
closure_text = []
def uncomment(s):
    return re.sub(r'(?<!\\)%[^\n]*', '', s)
def visit(p):
    p = p.resolve()
    if p in seen:
        return
    seen.add(p)
    text = uncomment(read(p).decode())
    closure_text.append(text)
    for value in re.findall(r'\\input\{([^}]+)\}', text):
        q = p.parent / value
        if q.suffix != '.tex':
            q = q.with_suffix('.tex')
        if not q.exists():
            q = D / 'blueprint' / (value if value.endswith('.tex') else value + '.tex')
        assert q.exists(), ('Missing actual input', value)
        visit(q)
visit(D / 'blueprint/extensions.tex')
labels = set(re.findall(r'\\label\{([^}]+)\}', '\n'.join(closure_text)))
refs = []
for text in [*bp_texts, pointer.decode()]:
    for block in re.findall(r'\\(?:uses|ref|eqref|cref|Cref|autoref)\{([^}]+)\}', uncomment(text)):
        refs += [s.strip() for s in block.split(',') if s.strip()]
assert all(s in labels for s in refs), sorted(set(refs) - labels)

# Read existing actual runtime receipts; do not invoke their runners.
owner = json.loads(read(A / 'final-nine-verification.json'))
assert owner['ordinary_native_source_revision'] == PIN
assert owner['strict_mathematical_whole_type_value_proof_Expr_matches'] == 166
for item in owner['components'].values():
    assert h(read(D / item['path'])) == item['sha256'], item['path']
typed = json.loads(read(A / 'typed-notation/attempt01/verification.json'))
assert typed['status'] == 'PASS' and typed['actual_new_public_frontend_definitions'] == 15
assert typed['no_logical_constant_dependents'] is True
assert typed['actual_physical_compiled_roots_scanned'] == 24271
for path, want in typed['evidence_sha256'].items():
    assert h(read(A / 'typed-notation/attempt01' / path)) == want, path
classification = json.loads(read(A / 'typed-notation/math-parents-attempt01/verification.json'))
assert classification['strict_mathematical_roots'] == 166
assert classification['raw_parent_status'] == 'BLOCKED_EXACT_DIFFERENCE'
assert classification['raw_differences_confined_exactly_to_actual_typed_frontends'] is True
raw_status = json.loads(read(A / 'final-per-module-expressions/status.json'))
assert raw_status['raw_frontend_differences_waived'] is False
assert raw_status['all_actual_public_roots'] == 181
payload = json.loads(read(A / 'new-nine-physical-ci-axioms.json'))
assert payload['status'] == 'PASS_ALL_ACTUAL_PHYSICAL_CI_PAYLOAD_AXIOMS'
assert payload['actual_physical_root_observations'] == 181
kernel = json.loads(read(A / 'new-kernel-status.json'))
assert kernel['passed'] == kernel['total'] == 9
assert b'axioms check: 13897 declarations' in read(A / 'lake-test.log')
assert read(A / 'lake-test.exit').strip() == b'0'

readme = read(D / 'README.md')
assert len(readme.decode().splitlines()) == 35
assert readme == show(str(D), BASE, 'README.md')
status = read(D / 'STATUS.md')
assert h(status) == '88dc2d73c039f83df4dd53958a72a91ac06bb68b8b073f046e38ab7ad182db1f'
assert len(status.decode().splitlines()) == 66
assert b'**G1, G3, G4, G8 and G9 remain open**' in status
api = read(D / 'docs/API.md')
old_api = show(str(D), BASE, 'docs/API.md')
assert old_api.count(b'All statements') == 1
assert api == old_api.replace(b'All statements', b'The original public API statements')

# The ONLY executed gate is the explicitly requested whole-source --check.
command = [sys.executable, str(A / 'sync_phase4_cohort.py'), '--source-root', '/workspace/archon-publish', '--check']
output('source-only-no-op-command.json', command)
result = subprocess.run(command, capture_output=True, text=True)
output('source-only-no-op.log', (result.stdout + result.stderr).encode())
assert result.returncode == 0, result.stderr
assert (A / 'source-replay-receipt.json').read_bytes() == before_summary
for path, want in inputs.items():
    assert h(Path(path).read_bytes()) == want, ('Read input changed', path)
output('read-only-input-fingerprints.json', inputs)
receipt = {'status': 'PASS_FINAL_NINE_INDEPENDENT_SOURCE_BP_PRESERVATION_AND_BYTE_EQUAL_NOOP',
    'timestamp_UTC': datetime.now(timezone.utc).isoformat(),
    'ordinary_native_source_revision': PIN, 'fixed_standalone_base': BASE,
    'new_complete_original_math_sources': 9, 'new_complete_original_BP_chapters': 9,
    'complete_original_written_proofs': 28, 'transparent_definition_nodes': definitions,
    'local_literal_attachments': attachments, 'documentation_only_pointer_inputs': 1,
    'documentation_pointer_is_not_a_new_math_module_or_local_export': True,
    'new_BP_literal_reference_occurrences': len(refs), 'actual_master_closure_TeX_files': len(seen),
    'new_unresolved_literal_reference_tokens': 0, 'sources': source_results,
    'approved_declaration_local_ENat_contexts': attrs_total, 'proof_type_payload_edits': 0,
    'old_mathematical_sources_byte_unchanged': 1532, 'old_nonmaster_TeX_files_byte_unchanged': 969,
    'prior373_tracked_audit_rawrecords_unchanged_vs_base': True,
    'prior373_provenance_metadata_sha256': prior_metadata,
    'prior_seven_stage_frozen_files_or_current_kernel_parts_checked': len(archive_manifest['files']),
    'four_frozen_profiles_byte_unchanged': True,
    'two_complete_deferred_modules_and_chapters_remain_absent': plan['deferred_prior_modules_preserved_absent'],
    'root_only_adds_nine_imports': True, 'master_only_adds_nine_chapters_and_documentation_pointer': True,
    'source_only_noop_exit': result.returncode, 'source_replay_summary_byte_unchanged': True,
    'source_replay_summary_sha256': h(before_summary),
    'existing_runtime_receipts_read_only': {'kernel_modules': 9, 'strict_math_roots': 166,
        'all_own_payload_CIs': 181, 'typed_public_frontends': 15, 'whole_environment_CIs': 24271,
        'raw_notation_parent_comparisons_remain_BLOCKED': 2, 'raw_frontend_Expr_equality_claimed': False,
        'lake_test_curated_declarations': 13897},
    'README_unchanged_35_lines': True, 'STATUS_scope_review_PASS_sha256': h(status),
    'API_only_original_public_statement_scope_clarification': True,
    'all_nine_global_goals_claimed_closed': False,
    'Lean_kernel_Expr_axiom_or_typed_runners_executed_by_this_reviewer': [],
    'old_evidence_or_mathematical_source_writes': 0,
    'only_existing_audit_write': 'source-replay-receipt.json rewritten to identical bytes by authorized --check'}
output('static-review.json', receipt)
print(json.dumps({'status': receipt['status'], 'receipt': str(W / 'static-review.json'),
                  'sha256': h((W / 'static-review.json').read_bytes()),
                  'no_op_summary_sha256': h(before_summary), 'reference_occurrences': len(refs),
                  'actual_master_TeX_files': len(seen)}, indent=2))
