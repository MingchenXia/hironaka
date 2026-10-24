from pathlib import Path
import json,hashlib
A=Path(__file__).resolve().parent
base=(A/'BoundedSelectedSupportV3.lean').read_text()
report=json.loads((A/'raw-complete-comparison.json').read_text())
roots=sorted({d['constant'][1] for d in report['differences'] if d['constant'][0]=='Hironaka.Support.ZeroCoordinateDerivativeUnivExact'})
assert len(roots)==6
selection='    let correctionRoots : List Lean.Name := ['+','.join(json.dumps(x)+'.toName' for x in roots)+']\n'
selection+='    selected := selected.toArray.filter (fun n => correctionRoots.contains (HironakaNativeMigrationCanonical.renamePrivate moduleRenames n)) |>.foldl (fun s n => s.insert n) ({} : Lean.NameSet)\n'
selection+='    unless selected.size == 6 do throw (IO.userError "Owner-correction scope must be exactly six actual generated roots")\n'
needle='    -- Map only private names occurring in complete expressions of every own\n'
assert base.count(needle)==1
out=base.replace(needle,selection+needle,1)
needle='    HironakaNativeMigrationCanonical.exportSelectedModuleData selected env oldModules renames oldOut'
replacement='''    -- Actual primitive binder contexts were inherited from the unchanged
    -- DerivativeIdealAlong primitive, not from the new theorem's physical owner.
    -- Preserve every exact private constant pair, numerical scope and Expr node.
    let actualOwnerRenames := renames.filter (fun p => (`_private).isPrefixOf p.1) ++
      [(`TranscendentalNakamaye.Pending.DerivativeIdealAlong, `Hironaka.MarkedIdeal.DerivativeIdealAlong)] ++ renames
    let some primitiveIdx := env.getModuleIdxFor? `Hironaka.DerivativeIdealAlong.iterDerivIdealAlong
      | throw (IO.userError "Missing actual unchanged primitive owner")
    unless env.header.moduleNames[primitiveIdx.toNat]! == `Hironaka.MarkedIdeal.DerivativeIdealAlong do
      throw (IO.userError "Unexpected actual primitive owner")
    IO.FS.writeFile (mapOut ++ ".actual-primitive-owner.json")
      (Lean.Json.mkObj [("primitive",Lean.toJson "Hironaka.DerivativeIdealAlong.iterDerivIdealAlong"),
        ("actual_imported_owner",Lean.toJson env.header.moduleNames[primitiveIdx.toNat]!.toString),
        ("corrected_original_roots",Lean.toJson selected.size),
        ("numerical_components_erased",Lean.toJson false)]).pretty
    HironakaNativeMigrationCanonical.exportSelectedModuleData selected env oldModules actualOwnerRenames oldOut'''
assert out.count(needle)==1;out=out.replace(needle,replacement,1)
out=out.replace('    HironakaNativeMigrationCanonical.exportModuleData env newModules [] newOut','    let _ := newOut -- reuse the immutable full public capture; no second public replay',1)
(A/'NarrowActualOwnerCorrectionV3.lean').write_text(out)
(A/'derivative-original-module.tsv').write_text('TranscendentalNakamaye.Pending.DerivativeIdealAlong\tHironaka.Support.ZeroCoordinateDerivativeUnivExact\n')
(A/'derivative-public-module.tsv').write_text('Hironaka.Support.ZeroCoordinateDerivativeUnivExact\tHironaka.Support.ZeroCoordinateDerivativeUnivExact\n')
(A/'owner-correction-scope.json').write_text(json.dumps({'status':'PREPARED_NECESSARY_NARROW_ACTUAL_OWNER_CORRECTION','original_roots':roots,'reason':'Raw original profile mapped inherited primitive binders to new support owner; actual public binder module contexts and unchanged primitive owner remain MarkedIdeal.DerivativeIdealAlong','new_profile_maps_only_module_prefix':True,'numerical_components_or_binders_erased':False,'unchanged_v3_serializer':True,'original_exact_rows_reused_verbatim':10,'original_rows_needing_fresh_correct_owner_capture':6,'raw_first_capture_retained':True},indent=2)+'\n')
print('PREPARED_NARROW_SIX_OWNER_CAPTURE')
