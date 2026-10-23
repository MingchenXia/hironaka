"""Actual new compiler-root types and whole public dependency scan; no Expr erasure."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent;D=A.parents[1]
N=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
R=Path('/workspace/archon-nakamaye/work/lean-runtime')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=A/'typed-notation'/('attempt'+(sys.argv[1]if len(sys.argv)>1 else '1'));assert not out.exists();out.mkdir(parents=True)
rows=json.loads((A/'provenance.json').read_text());mods=[r['destination_module']for r in rows]
owner=next(r for r in rows if r['source_module'].endswith('.HironakaActualTangentScalingImageFamily'))
sources=sorted([D/'Hironaka.lean',*(D/'Hironaka').rglob('*.lean')]);assert len(sources)==1559
fingerprints={str(p.relative_to(D)):h(p)for p in sources}
artifacts={str(p):h(p)for r in rows for p in[D/('.lake/build/lib/lean/'+r['destination_module'].replace('.','/')+'.olean')]}
native={str(p):h(p)for p in[N/(owner['source_module'].replace('.','/')+'.lean'),N/('.lake/build/lib/lean/'+owner['source_module'].replace('.','/')+'.olean')]}
template=D/'audit/canonical-elementary-family-and-local-producers-20261021/ParserLogicalIsolationAllNotationTemplate.lean'
text=template.read_text()
subs={'-- IMPORT_NATIVE_NOTATION_PARENTS':'import '+owner['source_module'],
 '-- PAIRS_EXPECTED_COUNTS':'    (`'+owner['source_module']+', `'+owner['destination_module']+', 4)',
 '-- NEW_MODULE_NAMES':',\n'.join('    `'+m for m in mods),
 '-- UPSTREAM_ONLY_NAMES':'','-- EXPECTED_GENERATED_PUBLIC':'    12','-- EXPECTED_WHOLE_MODULES':'    1559',
 '-- OUTPUT_JSON':'    '+json.dumps(str((out/'actual-typed-witness.json').relative_to(D)))}
for k,v in subs.items():assert text.count(k)==1;text=text.replace(k,v)
(out/'ActualTypedWitness.lean').write_text(text)
(out/'source-inputs.json').write_text(json.dumps(fingerprints,indent=2)+'\n')
(out/'public-artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
(out/'native-inputs.json').write_text(json.dumps(native,indent=2)+'\n')
plan={'new_modules':mods,'whole_source_module_count':1559,'actual_original_notation_module':owner['source_module'],'actual_public_notation_module':owner['destination_module'],'original_literal_clauses':4,'expected_frontend_definitions_per_side':12,'unchanged_template_sha256':h(template),'parser_body_structural_equality_claimed':False}
(out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
env=dict(os.environ,LEAN_NUM_THREADS='1');env['LEAN_PATH']=str(N/'.lake/build/lib/lean')+(':'+env['LEAN_PATH']if env.get('LEAN_PATH')else'')
cmd=[str(R/'lean-probe.sh'),'lake','env','lean',str(out/'ActualTypedWitness.lean')]
with(out/'probe.log').open('w')as f:p=subprocess.run(cmd,cwd=D,env=env,stdout=f,stderr=subprocess.STDOUT)
(out/'probe.exit').write_text(str(p.returncode)+'\n');assert p.returncode==0,'See preserved probe.log'
assert {str(p.relative_to(D)):h(p)for p in sorted([D/'Hironaka.lean',*(D/'Hironaka').rglob('*.lean')])}==fingerprints
assert all(h(Path(p))==v for p,v in (artifacts|native).items())
w=json.loads((out/'actual-typed-witness.json').read_text());assert len(w['actual_original_and_public_parser_roots'])==24 and w['direct_references_to_public_parser_roots']==[]
log=(out/'probe.log').read_text();assert 'error:'not in log and 'warning:'not in log
receipt={'status':'PASS_ACTUAL_TYPED_ROOTS_AND_WHOLE_ENVIRONMENT_LOGICAL_ISOLATION','exit':0,'source_and_artifacts_unchanged':True,'actual_public_frontend_definitions':12,'actual_original_and_public_typed_definitions':24,'whole_public_modules_scanned':w['all_public_moduleData_modules'],'actual_physical_compiled_roots_scanned':w['all_public_moduleData_constants'],'parser_body_structural_equality_claimed':False,'no_logical_constant_dependents':True,'all_raw_body_differences_retained_for_strict_comparator':True,'unchanged_accepted_template_sha256':h(template),'evidence_sha256':{str(p.name):h(p)for p in out.iterdir()if p.is_file()}}
(out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
