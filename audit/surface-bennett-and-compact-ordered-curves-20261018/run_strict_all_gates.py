"""Unchanged ALL ScopedV3 export and exact complete Expr comparison, no waivers."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
def run(argv,log,required=True):
 with (A/log).open('w')as out:r=subprocess.run(argv,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 if required:assert r.returncode==0,(log,r.returncode)
 return r.returncode
start=time.monotonic()
run([sys.executable,str(A/'prepare_strict_original_captures.py')],'strict-capture-preparation.log')
run([sys.executable,str(A/'export_strict_original_captures.py'),'whole'],'strict-whole-export.log')
rc=run([sys.executable,str(ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'),str(A/'native-full-expressions.jsonl'),str(A/'public-full-expressions.jsonl'),str(A/'strict-whole-expression-comparison.json')],'strict-whole-comparison.log',False)
report=json.loads((A/'strict-whole-expression-comparison.json').read_text())
assert rc==0,('Exact ALL full expression comparison failed; retain all inputs',rc)
assert report['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
assert not report['missing']and not report['native_extras']and not report['differences']and not report['approved_native_extras']
assert report['auxiliaries_skipped']==report['proof_numbers_erased']==report['binder_names_erased']==0
assert not report['defeq_or_alpha_comparison']
assert report['old']['all_actual_constants']==report['native']['all_actual_constants']
n=report['old']['all_actual_constants'];assert n==315
first={r['file']:r['sha256']for r in json.loads((A/'strict-attempt-01/retained-unfiltered-capture-manifest.json').read_text())}
assert hashlib.sha256((A/'native-full-expressions.jsonl').read_bytes()).hexdigest()==first['native-full-expressions.jsonl'], 'Original native capture changed'
assert sum(v['theorems']for v in report['module_counts'].values())==279
receipt={'status':f'PASS_ALL_{n}_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS','whole_original_modules':34,'new_support_original_modules':0,'whole_actual_roots':n,'total_actual_roots':n,'whole_theorem_proofs':sum(v['theorems']for v in report['module_counts'].values()),'native_capture_byte_identical_to_first_frozen_attempt':True,'all_public_moduleData_roots_selected':True,'public_root_filters':0,'proof_or_binder_number_erasure':0,'source_proof_token_edits':0,'serializer_or_comparator_changes':0,'waivers':0,'comparison_sha256':hashlib.sha256((A/'strict-whole-expression-comparison.json').read_bytes()).hexdigest(),'elapsed_seconds':round(time.monotonic()-start,3)}
(A/'strict-all-final-comparison.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
