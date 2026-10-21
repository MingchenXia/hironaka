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
  let dir := "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/support-prep/principal-parts/import-closure-preflight/"
  let targets := (← IO.FS.lines (dir ++ "uncaptured-native-modules.txt")).map String.toName
  let supportParents := (← IO.FS.lines (dir ++ "selected13-native-parents.txt")).map String.toName
  let selected := (← IO.FS.lines (dir ++ "selected13-original-names.txt")).map String.toName
  let mut imports := targets
  for m in supportParents do
    unless imports.contains m do imports := imports.push m
  unless selected.size == 13 do throw (IO.userError "Unexpected selected support count")
  let env ← importModules (imports.map fun m => {module := m}) {}
  let mut rows : Array Json := #[]
  let mut roots := 0
  let mut edges := 0
  for m in imports do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"Missing actual source owner {m}")
    for ci in env.header.moduleData[i]!.constants do
      let user := (privateToUserName? ci.name).getD ci.name
      unless targets.contains m || selected.any (·.isPrefixOf user) do continue
      roots := roots + 1
      for (field,deps) in #[("type",ci.type.getUsedConstants),
          ("whole_value",((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])] do
        let mut ordinary : Array Json := #[]
        for dep in deps do
          edges := edges + 1
          let canonical := renameNamespace dep
          unless canonical.toString.startsWith "Hironaka." do continue
          if diagnosticGenerated dep then continue
          ordinary := ordinary.push (toJson canonical.toString)
        rows := rows.push (Json.mkObj [("actual_source_parent",toJson m.toString),
          ("actual_source_declaration",toJson ci.name.toString),
          ("canonical_source_user_name",toJson (renameNamespace user).toString),
          ("field",toJson field),("ordinary_canonical_Hironaka_direct_callees",Json.arr ordinary)])
  let report := Json.mkObj [("status",toJson "UNCAPTURED91_AND_SELECTED13_DIRECT_IMPORT_OWNER_METADATA_ONLY"),
    ("uncaptured_original_parent_modules",toJson targets.size),
    ("selected_support_declarations",toJson selected.size),
    ("actual_imported_parent_modules",toJson imports.size),
    ("actual_roots_inspected",toJson roots),("all_direct_edges_inspected",toJson edges),
    ("actual_direct_callee_rows",Json.arr rows),
    ("whole_316_repeat_kernel_axiom_Expr_build_performed",toJson false),
    ("formal_gates_filtered",toJson false)]
  IO.FS.writeFile (dir ++ "uncaptured-and-selected-direct-callees.json") (Json.pretty report)
  IO.println s!"IMPORT_OWNER_METADATA uncaptured={targets.size} selected={selected.size} roots={roots} directEdges={edges}; no316repeat/kernel/Expr/build"
