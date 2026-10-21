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
  let parent := `TranscendentalNakamaye.Pending.StrictTransformComposition
  let start := `TranscendentalNakamaye.Pending.StrictTransformComposition.IsBlowupSequence.compactSpace_surjective
  let env ← importModules #[{module := parent}] {}
  let mut available : Std.HashSet String := {}
  for name in (← IO.FS.lines (dir ++ "selected11-available-canonical-names.txt")) do
    available := available.insert name
  let mut queue : Array Name := #[start]
  let mut seen : Std.HashSet Name := {}
  let mut cursor := 0
  let mut checked : Array Json := #[]
  let mut edges : Array Json := #[]
  let mut generated : Array Json := #[]
  let mut totalEdges := 0
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    if seen.contains name then continue
    seen := seen.insert name
    if seen.size > 128 then throw (IO.userError "Bounded successor closure exceeded128 new ordinary declarations")
    let some ci := env.find? name | throw (IO.userError s!"Missing recursively referenced original declaration {name}")
    let some idx := env.getModuleIdxFor? name | throw (IO.userError s!"Missing original owner {name}")
    checked := checked.push (Json.mkObj [("actual_original_name",toJson name.toString),
      ("canonical_name",toJson (renameNamespace name).toString),
      ("actual_original_owner",toJson env.header.moduleNames[idx.toNat]!.toString),
      ("whole_value_present",toJson (ci.value? (allowOpaque := true)).isSome)])
    for (field,deps) in #[("type",ci.type.getUsedConstants),
        ("whole_value",((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])] do
      for dep in deps do
        totalEdges := totalEdges + 1
        let canonical := renameNamespace dep
        unless canonical.toString.startsWith "Hironaka." || diagnosticGenerated dep do continue
        if diagnosticGenerated dep || dep.toString.endsWith "._f" then
          generated := generated.push (Json.mkObj [("source",toJson name.toString),
            ("field",toJson field),("actual_generated_dependency",toJson dep.toString)])
          continue
        if available.contains canonical.toString then continue
        edges := edges.push (Json.mkObj [("source",toJson name.toString),
          ("field",toJson field),("actual_dependency",toJson dep.toString),
          ("canonical_dependency",toJson canonical.toString)])
        unless seen.contains dep do queue := queue.push dep
  let report := Json.mkObj [("status",toJson "FINITE_ORDINARY_SUCCESSOR_METADATA_CLOSURE_NOT_A_PROOF_GATE"),
    ("starting_original_declaration",toJson start.toString),
    ("actual_imported_parent",toJson parent.toString),
    ("ordinary_declarations_requiring_source",Json.arr checked),
    ("ordinary_missing_dependency_edges",Json.arr edges),
    ("generated_helper_sightings_not_extraction_targets",Json.arr generated),
    ("total_direct_type_and_whole_value_edges",toJson totalEdges),
    ("remaining_unprocessed_queue",toJson (queue.size-cursor)),
    ("all316_repeat_or_Expr_or_kernel_or_build_run",toJson false),
    ("formal_gates_filtered",toJson false)]
  IO.FS.writeFile (dir ++ "compactSpace-recursive-successor-closure.json") (Json.pretty report)
  IO.println s!"COMPACTSPACE_RECURSIVE_ORDINARY_CLOSURE declarations={checked.size} edges={totalEdges} missingEdges={edges.size} pending={queue.size-cursor}; no316repeat/kernel/Expr/build"
