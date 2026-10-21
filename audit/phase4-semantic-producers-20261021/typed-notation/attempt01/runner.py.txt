"""New15 typed compiler definitions and their actual whole-library dependents.

Uses the unchanged accepted Lean witness template. No root, Expr, Name, number,
binder or theorem body normalization. Run once after the final nine build.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,os,ast,re,sys
sys.dont_write_bytecode=True
D=Path('/workspace/hironaka');N=Path('/workspace/archon-nakamaye/TranscendentalNakamaye');R=Path('/workspace/archon-nakamaye/work/lean-runtime');A=D/'audit/phase4-semantic-producers-20261021';OLD=D/'audit/canonical-elementary-family-and-local-producers-20261021'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['HironakaActualIntrinsicStableAmbientIso','HironakaActualLocallyFiniteLimitStrictTransforms','HironakaSharpActualIncidentCentreTraceResidual','HironakaActualDirectionalPivotNormality','HironakaActualExceptionalInitialGeneration','HironakaCompactOpenBlowupExtension','HironakaSharpActualDynamicIncidentHistory','HironakaCompactCosupportOpenTowerExtension','HironakaNormalCrossingsPermittedFinitePrephase']
owners={'HironakaActualDirectionalPivotNormality':3,'HironakaActualExceptionalInitialGeneration':2}
p=argparse.ArgumentParser();p.add_argument('attempt');args=p.parse_args();out=A/'typed-notation'/args.attempt;assert not out.exists()
assert all((D/'Hironaka/Resolution'/(m+'.lean')).is_file()for m in mods)
sources=sorted([D/'Hironaka.lean',*(D/'Hironaka').rglob('*.lean')]);assert len(sources)==1542
fingerprints={str(p.relative_to(D)):h(p)for p in sources}
native={str(p):h(p)for m in owners for p in[N/('TranscendentalNakamaye/Pending/'+m+'.lean'),N/('.lake/build/lib/lean/TranscendentalNakamaye/Pending/'+m+'.olean')]}
artifacts={str(p):h(p)for m in mods+['ROOT'] for p in[D/('.lake/build/lib/lean/'+('Hironaka'if m=='ROOT'else'Hironaka/Resolution/'+m)+'.olean')]}
templ=OLD/'ParserLogicalIsolationAllNotationTemplate.lean';text=templ.read_text()
subs={'-- IMPORT_NATIVE_NOTATION_PARENTS':'\n'.join('import TranscendentalNakamaye.Pending.'+m for m in owners),'-- PAIRS_EXPECTED_COUNTS':',\n'.join('    (`TranscendentalNakamaye.Pending.'+m+', `Hironaka.Resolution.'+m+', '+str(c)+')'for m,c in owners.items()),'-- NEW_MODULE_NAMES':',\n'.join('    `Hironaka.Resolution.'+m for m in mods),'-- UPSTREAM_ONLY_NAMES':'','-- EXPECTED_GENERATED_PUBLIC':'    15','-- EXPECTED_WHOLE_MODULES':'    1542','-- OUTPUT_JSON':'    '+json.dumps(str((out/'actual-typed-witness.json').relative_to(D)))}
for k,v in subs.items():assert text.count(k)==1;text=text.replace(k,v)
text += """
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
""" + ',\n'.join('    `Hironaka.Resolution.'+m for m in mods) + """
  ]
  let mut total := 0
  for target in targets do
    let some idx := env.header.moduleNames.findIdx? (· == target)
      | throwError "Missing actual new module {target}"
    let roots := env.header.moduleData[idx]!.constants
    for ci in roots do
      let mut axs : Array Name := #[]
      if ci matches .axiomInfo _ then axs := axs.push ci.name
      let deps := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
      for dep in deps do
        let depAxs ← collectAxioms dep
        for ax in depAxs do
          unless axs.contains ax do axs := axs.push ax
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Nonstandard actual own-payload axiom {ax} in {ci.name}"
      logInfo m!"NEW_ACTUAL_ROOT {target} {ci.name} AXIOMS {axs}"
    total := total + roots.size
  unless total == 181 do throwError "Unexpected all-new actual-root count {total}"
  logInfo m!"ALL_NEW_ACTUAL_OWN_TYPE_VALUE_ROOTS {total} standard axiom subsets only"
"""
out.mkdir();(out/'ActualTypedWitness.lean').write_text(text);(out/'source-inputs.json').write_text(json.dumps(fingerprints,indent=2)+'\n');(out/'native-inputs.json').write_text(json.dumps(native,indent=2)+'\n');(out/'public-artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
config={'new_module_count':9,'expected_whole_modules':1542,'owners':owners,'expected_public_frontend_definitions':15,'expected_native_and_public':30,'unchanged_template_sha256':h(templ)};(out/'plan.json').write_text(json.dumps(config,indent=2)+'\n');(out/'runner.py.txt').write_bytes(Path(__file__).read_bytes())
env=dict(os.environ);env['LEAN_PATH']=str(N/'.lake/build/lib/lean')+(':'+env['LEAN_PATH']if env.get('LEAN_PATH')else'')
cmd=['flock','-s',str(R/'hironaka-standalone-build.lock'),str(R/'lean-probe.sh'),'lake','env','lean',str(out/'ActualTypedWitness.lean')]
with(out/'probe.log').open('w')as f:r=subprocess.run(cmd,cwd=D,env=env,stdout=f,stderr=subprocess.STDOUT)
(out/'probe.exit').write_text(str(r.returncode)+'\n')
assert r.returncode==0,'See preserved probe.log'
current=sorted([D/'Hironaka.lean',*(D/'Hironaka').rglob('*.lean')]);assert{str(p.relative_to(D)):h(p)for p in current}==fingerprints
assert all(h(Path(p))==v for p,v in(native|artifacts).items())
log=(out/'probe.log').read_text();assert 'error:'not in log and 'warning:'not in log
w=json.loads((out/'actual-typed-witness.json').read_text());assert len(w['actual_original_and_public_parser_roots'])==30 and w['direct_references_to_public_parser_roots']==[]
receipt={'status':'PASS','exit':0,'source_and_artifacts_unchanged':True,'actual_new_public_frontend_definitions':15,'actual_original_and_public_typed_definitions':30,'whole_public_modules_scanned':w['all_public_moduleData_modules'],'actual_physical_compiled_roots_scanned':w['all_public_moduleData_constants'],'parser_body_structural_equality_claimed':False,'no_logical_constant_dependents':True,'all181_new_physical_CI_own_type_and_whole_value_transitive_axioms_checked':True,'all_raw_body_differences_retained_for_separate_comparator':True,'unchanged_accepted_template_sha256':h(templ),'evidence_sha256':{str(p.name):h(p)for p in out.iterdir()if p.is_file()}}
(out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
