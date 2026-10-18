import Lean
import Hironaka
import TranscendentalNakamaye.Pending.RiemannExtensionThin

/-! Read-only actual-environment audit. This does not assert structural
equality of the generated parser bodies and does not omit them from any
source, standard-axiom, or kernel inventory. -/
open Lean

run_cmd do
  let env ← getEnv
  let oldModule := `TranscendentalNakamaye.Pending.RiemannExtensionThin
  let newModule := `Hironaka.Analytic.RiemannExtensionThin
  let mut generated : Array (Name × ConstantInfo) := #[]
  for module in #[oldModule,newModule] do
    let some idx := env.header.moduleNames.findIdx? (· == module)
      | throwError "Missing actual module {module}"
    for ci in env.header.moduleData[idx]!.constants do
      let some user := privateToUserName? ci.name | continue
      unless user.toString.endsWith ".termE" || user.toString.contains "._aux_" do continue
      unless ci matches .defnInfo _ do
        throwError "Generated parser root is not a definition: {ci.name}"
      unless ci.type.isConstOf ``ParserDescr || ci.type.isConstOf ``Macro ||
          ci.type.isConstOf ``PrettyPrinter.Unexpander do
        throwError "Unexpected actual parser TYPE: {ci.name} : {repr ci.type}"
      unless (ci.value? (allowOpaque := true)).isSome do
        throwError "Missing entire actual generated value {ci.name}"
      generated := generated.push (module,ci)
  unless generated.size == 6 do throwError "Expected six actual parser roots, got {generated.size}"
  let publicNames := generated.filterMap fun (module,ci) =>
    if module == newModule then some ci.name else none
  unless publicNames.size == 3 do throwError "Expected exactly three public parser roots"
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
    for ci in env.header.moduleData[idx]!.constants do
      constantsCount := constantsCount+1
      if ci matches .thmInfo _ then theoremCount := theoremCount+1
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
  unless otherCount+3 == constantsCount do throwError "Actual root inventory lost a generated root"
  unless references.isEmpty do throwError "Parser roots occur in actual other types/bodies: {references}"
  let output := Json.mkObj [
    ("status",toJson "PASS_ACTUAL_COMPILER_TYPES_AND_NO_LOGICAL_CONSTANT_DEPENDENTS"),
    ("actual_original_and_public_parser_roots",Json.arr rows),
    ("all_public_moduleData_modules",toJson moduleCount),
    ("all_public_moduleData_constants",toJson constantsCount),
    ("all_public_moduleData_theorems",toJson theoremCount),
    ("other_actual_constants_scanned",toJson otherCount),
    ("direct_type_constant_edges_scanned",toJson typeEdges),
    ("direct_entire_value_constant_edges_scanned",toJson valueEdges),
    ("direct_references_to_three_public_parser_roots",Json.arr references),
    ("parser_body_structural_equality_claimed",toJson false),
    ("roots_excluded_from_kernel_or_axiom_inventory",toJson 0)]
  IO.FS.writeFile "audit/analytic-coefficient-dictionary-and-chosen-overlaps-20261015/parser-logical-isolation-final.json"
    output.pretty
  logInfo m!"PARSER_LOGICAL_ISOLATION modules={moduleCount} constants={constantsCount} other={otherCount} references={references.size}"
