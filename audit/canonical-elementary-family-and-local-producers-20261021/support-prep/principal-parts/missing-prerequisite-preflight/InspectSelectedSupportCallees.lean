import Lean

/-! Read-only actual metadata/direct-reference diagnostic. No proof checking,
axiom collection, expression DAG export, declaration rewriting, or gate filter.
The namespace map is the existing native-name-inventory map, unchanged. -/
open Lean

private def namespaceRules : List (Name × Name) := [(`TranscendentalNakamaye.FirstPass.NonKahlerLocus, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI2, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI3, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI4, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI, `Hironaka), (`TranscendentalNakamaye.Pending, `Hironaka), (`TranscendentalNakamaye.FirstPass, `Hironaka), (`TranscendentalNakamaye.Upstream, `Hironaka), (`TranscendentalNakamaye, `Hironaka)]

private def renameNamespace (n : Name) : Name := Id.run do
  for (a,b) in namespaceRules do
    if a.isPrefixOf n then return n.replacePrefix a b
  return n

private def diagnosticGenerated (n : Name) : Bool :=
  (privateToUserName? n).isSome || n.toString.startsWith "_private." ||
  [".eq_", ".match_", "._proof_", "._simp_", "._aux_"].any
    (fun tag => (n.toString.splitOn tag).length > 1)

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let dir := "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/support-prep/principal-parts/missing-prerequisite-preflight/"
  let targets := (← IO.FS.lines (dir ++ "selected11-original-names.txt")).map String.toName
  let parents := (← IO.FS.lines (dir ++ "selected11-native-parent-modules.txt")).map String.toName
  unless targets.size == 11 && parents.size == 8 do
    throw (IO.userError "Unexpected selected source payload inventory")
  let env ← importModules (parents.map fun m => {module := m}) {}
  let mut available : Std.HashSet String := {}
  for name in (← IO.FS.lines (dir ++ "selected11-available-canonical-names.txt")) do
    available := available.insert name
  let mut missing : Array Json := #[]
  let mut checked : Array Json := #[]
  let mut edges := 0
  for name in targets do
    let some ci := env.find? name | throw (IO.userError s!"Missing selected actual source declaration {name}")
    let some idx := env.getModuleIdxFor? name | throw (IO.userError s!"Missing actual selected source owner {name}")
    let owner := env.header.moduleNames[idx.toNat]!
    checked := checked.push (Json.mkObj [("actual_original_name",toJson name.toString),
      ("actual_original_owner",toJson owner.toString),
      ("whole_value_present",toJson (ci.value? (allowOpaque := true)).isSome)])
    for (field,deps) in #[("type",ci.type.getUsedConstants),
        ("whole_value",((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])] do
      for dep in deps do
        edges := edges + 1
        let canonical := renameNamespace dep
        unless canonical.toString.startsWith "Hironaka." do continue
        if diagnosticGenerated dep then continue
        if available.contains canonical.toString then continue
        let depOwner := match env.getModuleIdxFor? dep with
          | some i => env.header.moduleNames[i.toNat]!.toString
          | none => "<no-imported-module-owner>"
        missing := missing.push (Json.mkObj [("actual_source_declaration",toJson name.toString),
          ("field",toJson field),("original_dependency",toJson dep.toString),
          ("canonical_dependency",toJson canonical.toString),
          ("actual_original_dependency_owner",toJson depOwner)])
  let report := Json.mkObj [("status",toJson "SELECTED11_OLD_SOURCE_DIRECT_CALLEE_DIAGNOSTIC_ONLY"),
    ("selected_originals",Json.arr checked),("actual_parent_imports",toJson (parents.map Name.toString)),
    ("direct_type_and_whole_value_edges",toJson edges),
    ("nested_missing_callee_occurrences",Json.arr missing),
    ("kernel_or_axiom_or_expression_export_performed",toJson false),
    ("formal_gates_filtered",toJson false)]
  IO.FS.writeFile (dir ++ "selected11-successor-preflight.json") (Json.pretty report)
  IO.println s!"SELECTED_SUPPORT_DIRECT_CALLEES originals={targets.size} parents={parents.size} edges={edges} nestedMissing={missing.size}; no316repeat/kernel/Expr replay"
