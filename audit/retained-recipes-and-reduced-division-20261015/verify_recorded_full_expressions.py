"""Compare the recorded complete actual expressions with the frozen strict comparator.

This read-only audit replays captured expression data. Current source compilation,
standard-axiom auditing and frozen kernel replay are independent recorded checks.
"""
from pathlib import Path
import gzip, hashlib, json, subprocess, sys, tempfile, shutil
here=Path(__file__).resolve().parent
root=here.parents[1]
manifest=json.loads((here/'full-expression-artifacts.json').read_text())
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
comparator=root/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
assert sha(comparator)=='28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063'
accepted_support=json.loads((here/'fragment-full-expression-comparison.json').read_text())
assert accepted_support['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
assert sha(here/'fragment-native-full-expressions.jsonl')==accepted_support['old']['sha256']
assert sha(here/'fragment-public-full-expressions.jsonl')==accepted_support['native']['sha256']
with tempfile.TemporaryDirectory(prefix='hironaka-full-expressions-') as tmp:
    tmp=Path(tmp)
    for filename, rec in manifest.items():
        compressed=here/rec['compressed_path']
        assert sha(compressed)==rec['compressed_sha256']
        destination=tmp/filename
        with gzip.open(compressed,'rb') as source, destination.open('wb') as out:
            shutil.copyfileobj(source,out)
        assert destination.stat().st_size==rec['uncompressed_bytes']
        assert sha(destination)==rec['uncompressed_sha256']
    groups=[(tmp/'native-full-expressions.jsonl',tmp/'public-full-expressions.jsonl','whole',450),
            (here/'fragment-native-full-expressions.jsonl',here/'fragment-public-full-expressions.jsonl','support',2)]
    total=0
    for old,new,label,expected in groups:
        output=tmp/(label+'-comparison.json')
        subprocess.run([sys.executable,str(comparator),str(old),str(new),str(output)],check=True,stdout=subprocess.DEVNULL)
        report=json.loads(output.read_text())
        assert report['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
        assert not report['missing'] and not report['native_extras'] and not report.get('differences', [])
        assert report['fallbacks']==0 and report['auxiliaries_skipped']==0
        count=report['old']['all_actual_constants']
        assert count==report['native']['all_actual_constants']==expected
        total+=count
        print(label+': complete actual types and values match for '+str(count)+' roots')
    assert total==452
    print('PASS_ALL_452_RECORDED_ACTUAL_ROOTS_FULL_STRUCTURAL_COMPARISON')
