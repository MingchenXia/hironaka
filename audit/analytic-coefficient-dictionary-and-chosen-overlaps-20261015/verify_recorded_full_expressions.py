"""Recheck complete recorded expressions; does not replace current Lean checks.

The frozen comparator is unchanged. Exactly three actual typed parser outputs
are disclosed separately, and the raw all-root structural failure is retained.
"""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EXPECTED_COMPARATOR = '28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
COMPARATOR_REL = Path('audit/local-sharp-curves-20261015/compare_full_expr_dag.py')
assert hashlib.sha256((ROOT / COMPARATOR_REL).read_bytes()).hexdigest() == EXPECTED_COMPARATOR
classified = json.loads((HERE / 'all-actual-root-verification-classification-final.json').read_text())
classifier = HERE / 'compare_classified_actual_roots.py'
assert hashlib.sha256(classifier.read_bytes()).hexdigest() == classified['classifier_sha256']
manifest = json.loads((HERE / 'lossless-expression-snapshot-compression.json').read_text())
captures = {row['raw']: row for row in manifest['files']}
primary = ['native-full-expressions.jsonl', 'public-full-expressions-final.jsonl',
           'fragment-native-full-expressions.jsonl', 'fragment-public-full-expressions-final.jsonl']
with tempfile.TemporaryDirectory(prefix='hironaka-recorded-expressions-') as scratch:
    tmp_root = Path(scratch)
    target = tmp_root / HERE.relative_to(ROOT)
    target.mkdir(parents=True)
    comparator = tmp_root / COMPARATOR_REL
    comparator.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / COMPARATOR_REL, comparator)
    for name in primary:
        row = captures[name]
        compressed = HERE / row['gzip']
        assert hashlib.sha256(compressed.read_bytes()).hexdigest() == row['gzip_sha256']
        digest = hashlib.sha256()
        with gzip.open(compressed, 'rb') as src, (target / name).open('wb') as out:
            while data := src.read(1024 * 1024):
                digest.update(data)
                out.write(data)
        assert digest.hexdigest() == row['raw_sha256']
    for name in ['compare_classified_actual_roots.py', 'parser-logical-isolation.json']:
        shutil.copyfile(HERE / name, target / name)
    subprocess.run([sys.executable, str(target / classifier.name)], cwd=tmp_root, check=True)
    for side in ['native', 'public']:
        for kind in ['actual', 'mathematical']:
            name = f'{side}-all-{kind}-full-expressions-final.jsonl'
            assert hashlib.sha256((target / name).read_bytes()).hexdigest() == captures[name]['raw_sha256']
    for name in ['all-actual-root-verification-classification-final.json',
                 'all-actual-raw-structural-comparison-final.json',
                 'all-mathematical-strict-comparison-final.json']:
        actual = json.loads((target / name).read_text())
        expected = json.loads((HERE / name).read_text())
        if name != 'all-actual-root-verification-classification-final.json':
            kind = 'mathematical' if name == 'all-mathematical-strict-comparison-final.json' else 'actual'
            relatives = {'old': HERE.relative_to(ROOT) / f'native-all-{kind}-full-expressions-final.jsonl',
                         'native': HERE.relative_to(ROOT) / f'public-all-{kind}-full-expressions-final.jsonl',
                         'comparator': COMPARATOR_REL}
            for key, relative in relatives.items():
                assert Path(actual[key]['path']) == tmp_root / relative
                assert Path(expected[key]['path']).parts[-len(relative.parts):] == relative.parts
                # Only report file locations differ between checkouts. Every
                # captured byte/hash, AST comparison and result field is exact.
                del actual[key]['path']
                del expected[key]['path']
        assert actual == expected, name
print('PASS recorded complete mathematical types/values: 1006 roots, 839 theorem proofs.')
print('Raw all-1009-root structural comparison remains BLOCKED on exactly three disclosed parser outputs.')
print('Their typed source-generation audit, actual-root axiom audit and frozen kernel replay are separate gates.')
