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
  let old := (← IO.FS.lines (dir ++ "old-modules-e942.txt")).map String.toName
  let native := (← IO.FS.lines (dir ++ "native316-modules.txt")).map String.toName
  unless old.size == 1159 && native.size == 316 do
    throw (IO.userError "Unexpected fixed source-module inventory")
  let env ← importModules ((old ++ native).map fun m => {module := m}) {}
  let mut available : Std.HashSet String := {}
  for name in (← IO.FS.lines (dir ++ "new316-expected-canonical-names.txt")) do
    available := available.insert name
  let mut oldRows : Array Json := #[]
  let mut oldCount := 0
  for m in old do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"Missing actual OLD module {m}")
    let mut roots : Array Json := #[]
    for ci in env.header.moduleData[i]!.constants do
      available := available.insert ci.name.toString
      roots := roots.push (toJson ci.name.toString)
      oldCount := oldCount + 1
    oldRows := oldRows.push (Json.mkObj [("module",toJson m.toString),("actual_roots",Json.arr roots)])
  IO.FS.writeFile (dir ++ "old1159-actual-moduledata-names.json") (Json.pretty (Json.arr oldRows))
  let mut missing : Array Json := #[]
  let mut nativeRoots := 0
  let mut typeEdges := 0
  let mut valueEdges := 0
  let mut eligibleEdges := 0
  let mut excludedGeneratedEdges := 0
  for m in native do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"Missing actual native owner {m}")
    for ci in env.header.moduleData[i]!.constants do
      nativeRoots := nativeRoots + 1
      for (field,deps) in #[("type",ci.type.getUsedConstants),
          ("whole_value",((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])] do
        if field == "type" then typeEdges := typeEdges + deps.size
        else valueEdges := valueEdges + deps.size
        for dep in deps do
          let canonical := renameNamespace dep
          unless canonical.toString.startsWith "Hironaka." do continue
          if diagnosticGenerated dep then
            excludedGeneratedEdges := excludedGeneratedEdges + 1
            continue
          eligibleEdges := eligibleEdges + 1
          if available.contains canonical.toString then continue
          let originalOwner := match env.getModuleIdxFor? dep with
            | some idx => env.header.moduleNames[idx.toNat]!.toString
            | none => "<no-imported-module-owner>"
          missing := missing.push (Json.mkObj [
            ("source_parent_module",toJson m.toString),
            ("source_declaration",toJson ci.name.toString),
            ("canonical_source_declaration",toJson (renameNamespace ci.name).toString),
            ("field",toJson field),
            ("original_dependency",toJson dep.toString),
            ("canonical_dependency",toJson canonical.toString),
            ("actual_original_dependency_owner",toJson originalOwner)])
  let report := Json.mkObj [
    ("status",toJson "COMPLETE_OLD_METADATA_AND_NATIVE_DIRECT_CALLEE_DIAGNOSTIC_ONLY"),
    ("old_modules",toJson old.size),("old_actual_metadata_constants",toJson oldCount),
    ("native_parent_modules",toJson native.size),("native_actual_metadata_constants",toJson nativeRoots),
    ("direct_type_constant_edges",toJson typeEdges),("direct_whole_value_constant_edges",toJson valueEdges),
    ("eligible_canonical_Hironaka_edges",toJson eligibleEdges),
    ("diagnostic_only_generated_edges_excluded",toJson excludedGeneratedEdges),
    ("ordinary_missing_callee_occurrences",Json.arr missing),
    ("kernel_or_axiom_replay_performed",toJson false),
    ("expression_DAGs_exported",toJson false),("formal_gates_filtered",toJson false)]
  IO.FS.writeFile (dir ++ "native316-direct-callee-preflight.json") (Json.pretty report)
  IO.println s!"ACTUAL_PREREQUISITE_METADATA old={old.size}/{oldCount} native={native.size}/{nativeRoots} missingOccurrences={missing.size}; no kernel/axiom/Expr replay"
