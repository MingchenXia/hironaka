"""Replay the exact two original support proofs and the sole new-consumer import.

No old public mathematical source is changed. This bounded repair deliberately
does not claim that the later major publication cohort has been synchronized.
"""
from pathlib import Path
import argparse, ast, hashlib, json, re, subprocess, sys

parser = argparse.ArgumentParser()
parser.add_argument('--source-root', type=Path, required=True)
args = parser.parse_args()
audit = Path(__file__).resolve().parent
root = audit.parents[1]
sha = lambda data: hashlib.sha256(data).hexdigest()
record = json.loads((audit / 'original-support-source-provenance.json').read_text())
raw = subprocess.check_output([
    'git', '-C', str(args.source_root), 'show',
    record['published_native_revision'] + ':' + record['source_parent_path']])
assert sha(raw) == record['source_parent_sha256']
text = raw.decode()
sys.path.insert(0, str(root / 'scripts'))
import upstream_namespace_map as names
names.set_api_modules([
    f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'
                + '|'.join(flat) + r')\.(?=[\w«])')
frozen = root / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
function = next(n for n in ast.parse(frozen.read_text()).body
                if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
exec(compile(ast.Module(body=[function], type_ignores=[]), str(frozen), 'exec'))

pieces = record['original_context_pieces']
assert all(p['original_text'] in text and
           sha(p['original_text'].encode()) == p['sha256'] for p in pieces)
joined = '\n\n'.join(p['original_text'] for p in pieces)
expected = ('/- Two complete original coordinate-derivative prerequisites, with '
            'unchanged mathematical statements and proofs. -/\n'
            + ''.join('import ' + m + '\n'
                      for m in record['additional_existing_support_imports'])
            + '\n' + relocate(joined))
actual = (root / record['destination_path']).read_bytes()
assert actual == expected.encode()
assert sha(actual) == record['destination_sha256']
for item in record['source_complete_declarations']:
    lo, hi = item['source_byte_range']
    block = raw[lo:hi]
    assert sha(block) == item['original_declaration_sha256']
    assert expected.count(relocate(block.decode())) == 1

change = json.loads((audit / 'new-consumer-pure-support-import.json').read_text())
path = change['destination_module'].replace('.', '/') + '.lean'
before = subprocess.check_output([
    'git', '-C', str(root), 'show',
    'e9114c3050b73f9051288f673a3be107666137d9:' + path])
assert sha(before) == change['before_source_sha256']
assert before.decode().count(change['before']) == 1
after = before.decode().replace(change['before'], change['after'])
assert (root / path).read_bytes() == after.encode()
assert sha(after.encode()) == change['after_source_sha256']

previous = json.loads((audit / 'before-repair-public-source-guard.json').read_text())
old_sources = previous['mathematical_sources']
assert len(old_sources) == 1042
for path, digest in old_sources.items():
    assert sha((root / path).read_bytes()) == digest, path
guard = root / json.loads((audit / 'major-resumption-authorization.json').read_text())['historical_pause_guard']
assert sha(guard.read_bytes()) == json.loads((audit / 'major-resumption-authorization.json').read_text())['historical_pause_guard_sha256']

receipt = {
    'status': 'PASS_TWO_COMPLETE_ORIGINAL_PROOFS_AND_SOLE_NEW_CONSUMER_IMPORT',
    'published_native_revision': record['published_native_revision'],
    'complete_original_support_proofs': len(record['source_complete_declarations']),
    'old_public_sources_byte_identical': len(old_sources),
    'mathematical_proof_tokens_edited': 0,
    'new_consumer_changes_only_recorded_pure_support_import': True,
    'historical_pause_guard_unchanged': True,
    'private_ledger_required': False,
    'major_publication_cohort_claimed_synchronized': False,
}
(audit / 'repaired-original-source-replay.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
