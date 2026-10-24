"""Strict complete mathematical comparison after actual typed source isolation.

Retains all unfiltered captures and raw BLOCKED reports. No DAG, Name, number,
binder or proof normalization; unchanged accepted typed-capture helper and comparator.
"""
from pathlib import Path
import hashlib,importlib.util,json,subprocess,sys
D=Path('/workspace/hironaka');A=Path(__file__).resolve().parent
OLD=D/'audit/canonical-elementary-family-and-local-producers-20261021'
out=A/'typed-notation'/'math-parents-attempt2';assert not out.exists()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
vr=A/'typed-notation/attempt2/verification.json';v=json.loads(vr.read_text())
assert v['status']=='PASS_ACTUAL_TYPED_ROOTS_AND_WHOLE_ENVIRONMENT_LOGICAL_ISOLATION'and v['exit']==0
for n,x in v['evidence_sha256'].items():assert h(vr.parent/n)==x
w=json.loads((vr.parent/'actual-typed-witness.json').read_text())
assert len(w['actual_original_and_public_parser_roots'])==24 and not w['direct_references_to_public_parser_roots']
for name,x in json.loads((vr.parent/'source-inputs.json').read_text()).items():assert h(D/name)==x
for fn in ['native-inputs.json','public-artifacts.json']:
 for name,x in json.loads((vr.parent/fn).read_text()).items():assert h(Path(name))==x
helper=OLD/'compare_all_typed_notation_parents.py'
spec=importlib.util.spec_from_file_location('accepted_typed_capture',helper);c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
c.OWNERS={'HironakaActualTangentScalingImageFamily':4};c.SHORTS=list(c.OWNERS);c.GENERATED=12
assert h(c.COMPARATOR)==c.COMPARATOR_SHA
status_path=A/'final-per-module-expressions/status.json';st=json.loads(status_path.read_text());assert len(st['modules'])==14
out.mkdir();(out/'status-snapshot.json').write_bytes(status_path.read_bytes());(out/'classifier.py.txt').write_bytes(Path(__file__).read_bytes())
sides={side:c.capture(st,w,side,out)for side in ['original','public']}
assert sides['original']['all']==sides['public']['all']==73
assert sides['original']['mathematical']==sides['public']['mathematical']==61
reports={};exits={}
for mode in ['all','mathematical']:
 rp=out/(mode+'-comparison.json')
 with(out/(mode+'-comparison.log')).open('w')as f:p=subprocess.run([sys.executable,str(c.COMPARATOR),str(out/('original-'+mode+'.jsonl')),str(out/('public-'+mode+'.jsonl')),str(rp)],stdout=f,stderr=subprocess.STDOUT)
 exits[mode]=p.returncode;reports[mode]=json.loads(rp.read_text())
assert exits['all']==1 and reports['all']['status']=='BLOCKED_EXACT_DIFFERENCE'
oldkeys={(x['module'],x['name'])for x in sides['original']['parser']};newkeys={(x['module'],x['name'])for x in sides['public']['parser']}
blocked=reports['all'];assert all(tuple(k)in oldkeys for k in blocked['missing'])
assert all(tuple(k)in newkeys for k in blocked['native_extras'])
assert all(tuple(x['constant'])in oldkeys|newkeys for x in blocked['differences'])
assert exits['mathematical']==0 and reports['mathematical']['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH'
others=[]
for m,r in st['modules'].items():
 if m in {'Hironaka.Resolution.'+x for x in c.OWNERS}:continue
 p=D/r['folder']/'raw-complete-parent-comparison.json';j=json.loads(p.read_text())
 assert j['status']=='EXACT_ALL_FULL_EXPR_DAG_MATCH',m
 assert not j['missing']and not j['native_extras']and not j['differences']
 count=sum(x['constants']for x in j['module_counts'].values())
 others.append({'module':m,'actual_roots':count,'raw_report':str(p.relative_to(D)),'sha256':h(p)})
assert len(others)==13 and sum(x['actual_roots']for x in others)==251
rec={'status':'PASS_ALL312_MATHEMATICAL_ROOTS_STRICT_WITH12_DISCLOSED_TYPED_FRONTEND_DEFINITIONS','total_new_actual_physical_CI':324,'strict_mathematical_roots':312,'raw_exact_whole_modules':13,'typed_frontend_parent_modules':1,'parent_actual_roots':73,'parent_strict_mathematical_roots':61,'actual_public_typed_frontends':12,'actual_original_and_public_typed_frontends':24,'raw_parent_status':'BLOCKED_EXACT_DIFFERENCE','raw_differences_confined_exactly_to_actual_typed_frontends':True,'all_mathematical_fields_compared_with_unchanged_frozen_comparator':True,'no_type_value_proof_DAG_Name_number_binder_normalization':True,'parser_body_structural_equality_claimed':False,'old_module_whole_Expr_or_kernel_rechecks':0,'typed_witness_receipt':{'path':str(vr.relative_to(D)),'sha256':h(vr)},'unchanged_accepted_capture_helper':{'path':str(helper.relative_to(D)),'sha256':h(helper)},'comparator_sha256':h(c.COMPARATOR),'sides':sides,'thirteen_raw_exact_modules':others,'raw_status_input_sha256':h(status_path)}
(out/'verification.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:rec[k]for k in ['status','total_new_actual_physical_CI','strict_mathematical_roots','raw_exact_whole_modules','actual_public_typed_frontends']}),flush=True)
