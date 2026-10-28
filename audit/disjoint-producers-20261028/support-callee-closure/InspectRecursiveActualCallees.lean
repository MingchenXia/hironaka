import Lean

/-! One bounded actual native-CI metadata query. No kernel/axiom replay,
full expression DAG export or public/candidate source changes. -/
open Lean

private def namespaceRules : List (Name × Name) :=
  [(`TranscendentalNakamaye.FirstPass.NonKahlerLocus, `Hironaka),
   (`TranscendentalNakamaye.Pending.HironakaAPI2, `Hironaka),
   (`TranscendentalNakamaye.Pending.HironakaAPI3, `Hironaka),
   (`TranscendentalNakamaye.Pending.HironakaAPI4, `Hironaka),
   (`TranscendentalNakamaye.Pending.HironakaAPI, `Hironaka),
   (`TranscendentalNakamaye.Pending, `Hironaka),
   (`TranscendentalNakamaye.FirstPass, `Hironaka),
   (`TranscendentalNakamaye.Upstream, `Hironaka),
   (`TranscendentalNakamaye, `Hironaka)]

private def renameNamespace (n : Name) : Name := Id.run do
  for (a,b) in namespaceRules do
    if a.isPrefixOf n then return n.replacePrefix a b
  return n

private def diagnosticReason (n : Name) : Option String :=
  if (privateToUserName? n).isSome || n.toString.startsWith "_private." then
    some "private actual name; preserved separately, not an ordinary public helper"
  else if [".eq_", ".match_", "._match_", "._proof_", "._simp_", "._aux_"].any
      (fun tag => (n.toString.splitOn tag).length > 1) then
    some "generated equation/match/proof/simp/auxiliary helper name"
  else if n.toString.endsWith ".congr_simp" then
    some "generated congruence-simplification helper name"
  else if ["_hyg", "_@", "_elambda"].any (fun tag => (n.toString.splitOn tag).length > 1) then
    some "compiler hygiene/internal generated name"
  else none

private def actualCIKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def typeHeader (e : Expr) : Array Json := Id.run do
  let mut e := e
  let mut rows := #[]
  while true do
    match e with
    | .forallE n ty body _ =>
      rows := rows.push (Json.mkObj [("binder",toJson n.toString),
        ("actual_binder_type_used_constants",toJson (ty.getUsedConstants.map Name.toString))])
      e := body
    | _ => break
  return rows.push (Json.mkObj [("actual_result_type_used_constants",toJson (e.getUsedConstants.map Name.toString))])

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let dir := "/workspace/hironaka-phase5-main-integration/audit/disjoint-producers-20261028/support-callee-closure/"
  let modules := (← IO.FS.lines (dir ++ "native-parent-modules.txt")).map String.toName
  let seeds := (← IO.FS.lines (dir ++ "selected4-native-names.txt")).map String.toName
  unless modules.size == 3 && seeds.size == 4 do throw (IO.userError "Expected exactly3 real native parents and4 selected helpers")
  let env ← importModules (modules.map fun m => {module := m}) {}
  let mut available : Std.HashSet String := {}
  for fn in #["base-public-actual-names.txt","planned27-public-actual-names.txt"] do
    for name in (← IO.FS.lines (dir ++ fn)) do available := available.insert name
  for s in seeds do available := available.insert (renameNamespace s).toString
  let mut queue := seeds
  let mut queued : Std.HashSet String := {}
  for s in seeds do queued := queued.insert s.toString
  let mut cursor := 0
  let mut declarations : Array Json := #[]
  let mut rawEdges : Array Json := #[]
  let mut absentEdges : Array Json := #[]
  let mut diagnostics : Array Json := #[]
  let mut unresolved : Array Json := #[]
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor+1
    let some ci := env.find? name | throw (IO.userError s!"Actual queued native CI absent: {name}")
    let some ownerIdx := env.getModuleIdxFor? name | throw (IO.userError s!"No actual imported owner: {name}")
    let owner := env.header.moduleNames[ownerIdx.toNat]!
    let inPhysical := env.header.moduleData[ownerIdx.toNat]!.constants.any (fun x => x.name == name)
    let actualOlean ← findOLean owner
    declarations := declarations.push (Json.mkObj [("actual_native_name",toJson name.toString),
      ("relocated_ordinary_name",toJson (renameNamespace name).toString),
      ("actual_native_owner",toJson owner.toString),("actual_kind",toJson (actualCIKind ci)),
      ("actual_physical_owner_contains_CI",toJson inPhysical),
      ("actual_native_olean_path",toJson actualOlean.toString),
      ("actual_type_universe_parameters",toJson (ci.levelParams.map Name.toString)),
      ("actual_type_binder_and_result_constant_metadata",Json.arr (typeHeader ci.type)),
      ("actual_type_used_constants",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("is_seed8",toJson (seeds.contains name))])
    for (field,deps) in #[("type",ci.type.getUsedConstants),
        ("whole_value",((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])] do
      for dep in deps do
        let canonical := renameNamespace dep
        let depOwner := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx.toNat]!.toString
          | none => "<no-imported-module-owner>"
        let isProject := canonical.toString.startsWith "Hironaka."
        let reason := diagnosticReason dep
        let availableAlready := available.contains canonical.toString
        let ordinaryMissing := isProject && reason.isNone && !availableAlready
        let row := [("caller_native_name",toJson name.toString),("caller_actual_owner",toJson owner.toString),
          ("field",toJson field),("native_callee",toJson dep.toString),
          ("relocated_ordinary_callee",toJson canonical.toString),
          ("actual_callee_lookup_owner",toJson depOwner),
          ("in_base_or_planned40_or_selected8",toJson availableAlready),
          ("project_namespace",toJson isProject),("ordinary_missing",toJson ordinaryMissing)]
        rawEdges := rawEdges.push (Json.mkObj row)
        if let some why := reason then
          diagnostics := diagnostics.push (Json.mkObj (("diagnostic_reason",toJson why)::row))
          continue
        unless ordinaryMissing do continue
        absentEdges := absentEdges.push (Json.mkObj row)
        if (env.find? dep).isNone then
          unresolved := unresolved.push (toJson dep.toString)
        else if !queued.contains dep.toString then
          queued := queued.insert dep.toString
          queue := queue.push dep
  IO.FS.writeFile (dir ++ "actual-native-declaration-metadata.json") (Json.pretty (Json.arr declarations))
  IO.FS.writeFile (dir ++ "all-raw-direct-callee-edges.json") (Json.pretty (Json.arr rawEdges))
  IO.FS.writeFile (dir ++ "private-generated-diagnostics.json") (Json.pretty (Json.arr diagnostics))
  IO.FS.writeFile (dir ++ "additional-ordinary-absent-edges.json") (Json.pretty (Json.arr absentEdges))
  let report := Json.mkObj [("status",toJson "RECURSIVE_ORDINARY_METADATA_CLOSURE_COMPLETE"),
    ("seed_count",toJson seeds.size),("imported_real_native_parents",toJson modules.size),
    ("processed_native_CIs",toJson declarations.size),("additional_ordinary_helpers",toJson (queue.size-seeds.size)),
    ("all_raw_direct_edges",toJson rawEdges.size),("private_generated_diagnostic_edges",toJson diagnostics.size),
    ("additional_ordinary_missing_edge_observations",toJson absentEdges.size),
    ("actual_native_CIs_unresolved",Json.arr unresolved),
    ("ordinary_queue_closed",toJson (cursor == queue.size && unresolved.isEmpty)),
    ("full_Expr_DAG_export",toJson false),("kernel_or_axiom_replay",toJson false),
    ("builds",toJson (0 : Nat)),("formal_roots_filtered",toJson false)]
  IO.FS.writeFile (dir ++ "recursive-ordinary-metadata-summary.json") (Json.pretty report)
  IO.println s!"RECURSIVE_NATIVE_HELPERS seeds={seeds.size} total={declarations.size} additional={queue.size-seeds.size} rawEdges={rawEdges.size} diagnostics={diagnostics.size} unresolved={unresolved.size}; metadata only"
