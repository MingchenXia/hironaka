import Lean
import Hironaka
import TranscendentalNakamaye.Pending.HironakaActualDirectionalPivotNormality
import TranscendentalNakamaye.Pending.HironakaActualExceptionalInitialGeneration

/-! Actual typed compiler roots and whole-public-environment dependency audit.
No generated body is erased or asserted structurally equal. All actual roots
remain subject to the separate kernel and transitive-axiom inventories. -/
open Lean
set_option maxHeartbeats 0
set_option maxRecDepth 10000

run_cmd do
  let env ← getEnv
  let pairs : Array (Name × Name × Nat) := #[
    (`TranscendentalNakamaye.Pending.HironakaActualDirectionalPivotNormality, `Hironaka.Resolution.HironakaActualDirectionalPivotNormality, 3),
    (`TranscendentalNakamaye.Pending.HironakaActualExceptionalInitialGeneration, `Hironaka.Resolution.HironakaActualExceptionalInitialGeneration, 2)
  ]
  let newModules : Array Name := #[
    `Hironaka.Resolution.HironakaActualIntrinsicStableAmbientIso,
    `Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms,
    `Hironaka.Resolution.HironakaSharpActualIncidentCentreTraceResidual,
    `Hironaka.Resolution.HironakaActualDirectionalPivotNormality,
    `Hironaka.Resolution.HironakaActualExceptionalInitialGeneration,
    `Hironaka.Resolution.HironakaCompactOpenBlowupExtension,
    `Hironaka.Resolution.HironakaSharpActualDynamicIncidentHistory,
    `Hironaka.Resolution.HironakaCompactCosupportOpenTowerExtension,
    `Hironaka.Resolution.HironakaNormalCrossingsPermittedFinitePrephase
  ]
  let upstreamOnlyNames : Array Name := #[

  ]
  for name in upstreamOnlyNames do
    unless (env.find? name).isNone do
      throwError "Upstream-only blueprint binding is actually exported locally: {name}"
  let expectedPublic : Nat :=
    15
  let frontendTag (ci : ConstantInfo) : Option Nat :=
    if ci.type.isConstOf ``ParserDescr then some 0
    else if ci.type.isConstOf ``Macro then some 1
    else if ci.type.isConstOf ``PrettyPrinter.Unexpander then some 2 else none
  let mut generated : Array (Name × ConstantInfo) := #[]
  let mut publicNames : Array Name := #[]
  for (oldModule,newModule,clauses) in pairs do
    for module in #[oldModule,newModule] do
      let some idx := env.header.moduleNames.findIdx? (· == module)
        | throwError "Missing actual notation owner {module}"
      let mut counts : Array Nat := #[0,0,0]
      for ci in env.header.moduleData[idx]!.constants do
        let some tag := frontendTag ci | continue
        unless ci matches .defnInfo _ do
          throwError "Typed notation root is not a definition: {ci.name}"
        unless (privateToUserName? ci.name).isSome do
          throwError "Typed notation root is not private: {ci.name}"
        unless (ci.value? (allowOpaque := true)).isSome do
          throwError "Missing whole generated body {ci.name}"
        generated := generated.push (module,ci)
        if module == newModule then publicNames := publicNames.push ci.name
        counts := counts.set! tag (counts[tag]!+1)
      unless counts == #[clauses,clauses,clauses] do
        throwError "Unexpected exact notation type inventory {module}: {counts}"
  unless generated.size == 2*expectedPublic && publicNames.size == expectedPublic do
    throwError "Unexpected actual typed notation inventory: {generated.size}/{publicNames.size}"
  let mut rows : Array Json := #[]
  for (module,ci) in generated do
    let typeName := if ci.type.isConstOf ``ParserDescr then "Lean.ParserDescr"
      else if ci.type.isConstOf ``Macro then "Lean.Macro"
      else "Lean.PrettyPrinter.Unexpander"
    rows := rows.push (Json.mkObj [
      ("actual_module_owner",toJson module.toString),
      ("actual_name",toJson ci.name.toString),
      ("actual_type",toJson typeName),
      ("kind",toJson "definition"),
      ("whole_value_present",toJson true)])
  let mut moduleCount := 0
  let mut newModuleCount := 0
  let mut constantsCount := 0
  let mut otherCount := 0
  let mut theoremCount := 0
  let mut typeEdges := 0
  let mut valueEdges := 0
  let mut references : Array Json := #[]
  for idx in [:env.header.moduleNames.size] do
    let module := env.header.moduleNames[idx]!
    unless module.toString == "Hironaka" || module.toString.startsWith "Hironaka." do continue
    moduleCount := moduleCount+1
    if newModules.contains module then newModuleCount := newModuleCount+1
    for ci in env.header.moduleData[idx]!.constants do
      constantsCount := constantsCount+1
      if ci matches .thmInfo _ then theoremCount := theoremCount+1
      if newModules.contains module && (frontendTag ci).isSome &&
          !publicNames.contains ci.name then
        throwError "Unclassified actual frontend root in new module {module}: {ci.name}"
      if publicNames.contains ci.name then continue
      otherCount := otherCount+1
      for dep in ci.type.getUsedConstants do
        typeEdges := typeEdges+1
        if publicNames.contains dep then
          references := references.push (Json.mkObj [
            ("module",toJson module.toString),("name",toJson ci.name.toString),
            ("field",toJson "type"),("direct_constant",toJson dep.toString)])
      for dep in ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] do
        valueEdges := valueEdges+1
        if publicNames.contains dep then
          references := references.push (Json.mkObj [
            ("module",toJson module.toString),("name",toJson ci.name.toString),
            ("field",toJson "whole_value"),("direct_constant",toJson dep.toString)])
  unless moduleCount ==
    1542
    do throwError "Unexpected whole standalone module count {moduleCount}"
  unless newModuleCount == newModules.size do
    throwError "New physical module is absent from actual import closure: {newModuleCount}/{newModules.size}"
  unless otherCount+expectedPublic == constantsCount do
    throwError "Actual root inventory lost a generated root"
  unless references.isEmpty do
    throwError "Parser roots occur in actual other types/bodies: {references}"
  let output := Json.mkObj [
    ("status",toJson "PASS_ACTUAL_COMPILER_TYPES_AND_NO_LOGICAL_CONSTANT_DEPENDENTS"),
    ("actual_original_and_public_parser_roots",Json.arr rows),
    ("all_public_moduleData_modules",toJson moduleCount),
    ("actual_new_moduleData_modules",toJson newModuleCount),
    ("all_public_moduleData_constants",toJson constantsCount),
    ("all_public_moduleData_theorems",toJson theoremCount),
    ("other_actual_constants_scanned",toJson otherCount),
    ("direct_type_constant_edges_scanned",toJson typeEdges),
    ("direct_entire_value_constant_edges_scanned",toJson valueEdges),
    ("direct_references_to_public_parser_roots",Json.arr references),
    ("actual_upstream_only_public_names_verified_absent",toJson (upstreamOnlyNames.map Name.toString)),
    ("parser_body_structural_equality_claimed",toJson false),
    ("roots_excluded_from_kernel_or_axiom_inventory",toJson 0)]
  IO.FS.writeFile
    "audit/phase4-semantic-producers-20261021/typed-notation/attempt01/actual-typed-witness.json"
    output.pretty
  logInfo m!"PARSER_LOGICAL_ISOLATION modules={moduleCount} new={newModuleCount} constants={constantsCount} other={otherCount} references={references.size}"

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Hironaka.Resolution.HironakaActualIntrinsicStableAmbientIso,
    `Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms,
    `Hironaka.Resolution.HironakaSharpActualIncidentCentreTraceResidual,
    `Hironaka.Resolution.HironakaActualDirectionalPivotNormality,
    `Hironaka.Resolution.HironakaActualExceptionalInitialGeneration,
    `Hironaka.Resolution.HironakaCompactOpenBlowupExtension,
    `Hironaka.Resolution.HironakaSharpActualDynamicIncidentHistory,
    `Hironaka.Resolution.HironakaCompactCosupportOpenTowerExtension,
    `Hironaka.Resolution.HironakaNormalCrossingsPermittedFinitePrephase
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
