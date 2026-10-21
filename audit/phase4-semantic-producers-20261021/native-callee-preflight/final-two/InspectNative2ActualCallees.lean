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

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let dir := "/workspace/archon-nakamaye/work/g1-g9-20261021-phase4/publication-final-two/"
  let modules := (← IO.FS.lines (dir ++ "native2-modules.txt")).map String.toName
  unless modules.size == 2 do throw (IO.userError "Expected exactly 2 native owners")
  let env ← importModules (modules.map fun m => {module := m}) {}
  let mut available : Std.HashSet String := {}
  for name in (← IO.FS.lines (dir ++ "base-and-seven-public-actual-names.txt")) do
    available := available.insert name
  -- Seed availability from EVERY actual new physical CI, not a filtered manifest.
  for m in modules do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"Missing actual new owner {m}")
    for ci in env.header.moduleData[i]!.constants do
      available := available.insert (renameNamespace ci.name).toString
  let mut roots : Array Json := #[]
  let mut unexpected : Array Json := #[]
  let mut absentOrdinary : Array Json := #[]
  let mut diagnostics : Array Json := #[]
  let mut allOrdinary : Array Json := #[]
  let mut ordinaryEdges := 0
  let mut diagnosticEdges := 0
  let mut typeEdges := 0
  let mut valueEdges := 0
  for m in modules do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"No actual native moduleData owner {m}")
    for ci in env.header.moduleData[i]!.constants do
      roots := roots.push (Json.mkObj [("module",toJson m.toString),("actual_name",toJson ci.name.toString)])
      for (field,deps) in #[("type",ci.type.getUsedConstants),
          ("whole_value",((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])] do
        if field == "type" then typeEdges := typeEdges + deps.size
        else valueEdges := valueEdges + deps.size
        for dep in deps do
          let canonical := renameNamespace dep
          unless canonical.toString.startsWith "Hironaka." || dep.toString.startsWith "_private." do continue
          let owner := match env.getModuleIdxFor? dep with
            | some idx => env.header.moduleNames[idx.toNat]!.toString
            | none => "<no-imported-module-owner>"
          let row := [("native_owner_module",toJson m.toString),
            ("native_source_declaration",toJson ci.name.toString),("field",toJson field),
            ("native_callee",toJson dep.toString),("relocated_callee",toJson canonical.toString),
            ("actual_native_callee_lookup_owner",toJson owner),
            ("available_in_captured_base_or_planned40",toJson (available.contains canonical.toString))]
          if let some why := diagnosticReason dep then
            diagnosticEdges := diagnosticEdges + 1
            diagnostics := diagnostics.push (Json.mkObj (("diagnostic_reason",toJson why)::row))
            continue
          allOrdinary := allOrdinary.push (Json.mkObj row)
          ordinaryEdges := ordinaryEdges + 1
          unless available.contains canonical.toString do
            absentOrdinary := absentOrdinary.push (Json.mkObj row)
  unless roots.size == 17 && unexpected.isEmpty do
    throw (IO.userError s!"Actual native2 metadata differed from expected17: roots={roots.size}, unexpectedCount={unexpected.size}")
  IO.FS.writeFile (dir ++ "native2-actual-physical-roots.json") (Json.pretty (Json.arr roots))
  IO.FS.writeFile (dir ++ "all-ordinary-direct-callee-edges.json") (Json.pretty (Json.arr allOrdinary))
  IO.FS.writeFile (dir ++ "private-generated-diagnostics.json") (Json.pretty (Json.arr diagnostics))
  let report := Json.mkObj [("status",toJson "ACTUAL_NATIVE2_METADATA_DIRECT_CALLEE_AVAILABILITY_ONLY"),
    ("native_modules",toJson modules.size),("actual_physical_CIs",toJson roots.size),
    ("direct_type_constant_edges",toJson typeEdges),("direct_whole_value_constant_edges",toJson valueEdges),
    ("ordinary_Hironaka_callee_edges",toJson ordinaryEdges),("private_generated_diagnostic_edges",toJson diagnosticEdges),
    ("available_distinct_names",toJson available.size),
    ("ordinary_absent_occurrences",Json.arr absentOrdinary),
    ("private_generated_diagnostics_preserved_separately",toJson true),
    ("formal_gates_filtered",toJson false),("kernel_or_axiom_replay",toJson false),
    ("full_Expr_DAG_export",toJson false),("production_source_changes",toJson false)]
  IO.FS.writeFile (dir ++ "native2-direct-callee-availability.json") (Json.pretty report)
  IO.println s!"NATIVE2_METADATA modules={modules.size} CIs={roots.size} missingOrdinaryOccurrences={absentOrdinary.size} diagnosticEdges={diagnosticEdges}; no kernel/axiom/Expr replay"
