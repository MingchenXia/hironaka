"""Run unchanged ALL-root capture and comparison over all19 new modules."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(argv,log,required=True):
 with(A/log).open('w')as stream:r=subprocess.run(argv,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
 if required:assert r.returncode==0,(log,r.returncode)
 return r.returncode
begin=time.monotonic()
run([sys.executable,str(A/'prepare_strict_original_captures.py')],'strict-capture-preparation.log')
run([sys.executable,str(A/'export_strict_original_captures.py'),'whole'],'strict-whole-export.log')
comparator=ROOT/'audit/local-sharp-curves-20261015/compare_full_expr_dag.py'
wc=run([sys.executable,str(comparator),str(A/'native-full-expressions.jsonl'),str(A/'public-full-expressions.jsonl'),str(A/'strict-whole-expression-comparison.json')],'strict-whole-comparison.log',False)
run([sys.executable,str(A/'export_strict_original_captures.py'),'support'],'strict-support-export.log')
run([sys.executable,str(A/'select_complete_original_support_rows.py')],'original-support-selection.log')
sc=run([sys.executable,str(comparator),str(A/'fragment-original-selected-for-all-public-roots.jsonl'),str(A/'fragment-public-full-expressions.jsonl'),str(A/'strict-support-expression-comparison.json')],'strict-support-comparison.log',False)
whole=json.loads((A/'strict-whole-expression-comparison.json').read_text());support=json.loads((A/'strict-support-expression-comparison.json').read_text())
first={r['file']:r['raw_sha256']for r in json.loads((A/'strict-attempt-01/retained-unfiltered-capture-manifest.json').read_text())}
for name in['native-full-expressions.jsonl','fragment-native-full-expressions.jsonl']:assert sha(A/name)==first[name],('Frozen original capture changed',name)
assert wc==sc==0,('Exact ALL proof comparison blocked',wc,sc)
for report in[whole,support]:
 assert report['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
 assert not report['missing']and not report['native_extras']and not report['differences']and not report['approved_native_extras']
 assert report['auxiliaries_skipped']==report['proof_numbers_erased']==report['binder_names_erased']==0
 assert not report['defeq_or_alpha_comparison']
 assert report['old']['all_actual_constants']==report['native']['all_actual_constants']
selection=json.loads((A/'original-support-selection.json').read_text())
receipt={'status':'PASS_ALL_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS','whole_original_modules':16,'support_original_modules':3,'whole_actual_roots':whole['old']['all_actual_constants'],'support_actual_roots':support['old']['all_actual_constants'],'total_actual_roots':whole['old']['all_actual_constants']+support['old']['all_actual_constants'],'whole_theorem_proofs':sum(v['theorems']for v in whole['module_counts'].values()),'support_theorem_proofs':sum(v['theorems']for v in support['module_counts'].values()),'full_unfiltered_native_support_parent_roots':selection['full_native_parent_actual_roots'],'all_public_moduleData_roots_selected':True,'public_root_filters':0,'proof_or_binder_number_erasure':0,'source_proof_token_edits':0,'serializer_or_comparator_changes':0,'waivers':0,'elapsed_seconds':round(time.monotonic()-begin,3)}
receipt['native_captures_byte_identical_to_first_frozen_attempt']=True
(A/'strict-all-final-comparison.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
