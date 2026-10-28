import Lean

/-! Actual compiled metadata only: no kernel replay or expression rewriting.
Every selected native physical CI and every project type/whole-value callee is
retained. Generated/private diagnostics do not filter later formal gates. -/
open Lean

private def renameNamespace (n : Name) : Name := Id.run do
  for (a,b) in [
      (`TranscendentalNakamaye.FirstPass.NonKahlerLocus, `Hironaka),
      (`TranscendentalNakamaye.Pending.HironakaAPI2, `Hironaka),
      (`TranscendentalNakamaye.Pending.HironakaAPI3, `Hironaka),
      (`TranscendentalNakamaye.Pending.HironakaAPI4, `Hironaka),
      (`TranscendentalNakamaye.Pending.HironakaAPI, `Hironaka),
      (`TranscendentalNakamaye.Pending, `Hironaka),
      (`TranscendentalNakamaye.FirstPass, `Hironaka),
      (`TranscendentalNakamaye.Upstream, `Hironaka),
      (`TranscendentalNakamaye, `Hironaka)] do
    if a.isPrefixOf n then return n.replacePrefix a b
  return n

private def diagnostic (n : Name) : Bool :=
  (privateToUserName? n).isSome || n.toString.startsWith "_private." ||
    [".eq_", ".match_", "._match_", "._proof_", "._simp_", "._aux_",
      ".congr_simp", "_hyg", "_@", "_elambda"].any
      (fun s => (n.toString.splitOn s).length > 1)

def main (args : List String) : IO UInt32 := do
  let [moduleFile,outFile] := args
    | throw (IO.userError "Expected native-module roster and output path")
  initSearchPath (← findSysroot)
  let modules := (← IO.FS.lines moduleFile).map String.toName
  let env := (← importModules ((#[`Hironaka] ++ modules).map fun m => {module := m}) {}).setExporting false
  let mut oldOwners : Std.HashMap Name (Array Name) := {}
  let mut newOwners : Std.HashMap Name (Array Name) := {}
  let mut oldRoots : Array Json := #[]
  let mut roots : Array Json := #[]
  let mut edges : Array Json := #[]
  let mut missing : Array Json := #[]
  let mut collisions : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (`Hironaka).isPrefixOf m then
      for ci in env.header.moduleData[i]!.constants do
        oldOwners := oldOwners.insert ci.name ((oldOwners.getD ci.name #[]).push m)
        oldRoots := oldRoots.push (Json.mkObj [("module",toJson m.toString),
          ("actual_name",toJson ci.name.toString)])
  for m in modules do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"No actual moduleData owner {m}")
    for ci in env.header.moduleData[i]!.constants do
      let canonical := renameNamespace ci.name
      newOwners := newOwners.insert canonical ((newOwners.getD canonical #[]).push m)
      roots := roots.push (Json.mkObj [("module",toJson m.toString),
        ("actual_name",toJson ci.name.toString),("canonical_name",toJson canonical.toString),
        ("private_or_generated_diagnostic",toJson (diagnostic ci.name))])
      if oldOwners.contains canonical then
        collisions := collisions.push (Json.mkObj [("native_module",toJson m.toString),
          ("native_name",toJson ci.name.toString),("canonical_name",toJson canonical.toString),
          ("existing_public_physical_owners",toJson ((oldOwners.getD canonical #[]).map Name.toString))])
  for m in modules do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throw (IO.userError s!"No actual owner {m}")
    for ci in env.header.moduleData[i]!.constants do
      let value := ci.value? (allowOpaque := true)
      match ci with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless value.isSome do throw (IO.userError s!"No whole physical value {ci.name}")
      | _ => pure ()
      for (field,deps) in #[("type",ci.type.getUsedConstants),
          ("whole_value",(value.map Expr.getUsedConstants).getD #[])] do
        for dep in deps do
          unless (`TranscendentalNakamaye).isPrefixOf dep || dep.toString.startsWith "_private." do continue
          let canonical := renameNamespace dep
          let owner := match env.getModuleIdxFor? dep with
            | some j => env.header.moduleNames[j.toNat]!.toString
            | none => "<no-imported-owner>"
          let available := oldOwners.contains canonical || newOwners.contains canonical
          let row := Json.mkObj [("native_caller_module",toJson m.toString),
            ("native_caller_root",toJson ci.name.toString),("field",toJson field),
            ("native_callee",toJson dep.toString),("canonical_callee",toJson canonical.toString),
            ("actual_native_callee_owner",toJson owner),
            ("existing_public_physical_owners",toJson ((oldOwners.getD canonical #[]).map Name.toString)),
            ("planned_new_original_owners",toJson ((newOwners.getD canonical #[]).map Name.toString)),
            ("available",toJson available),("private_or_generated_diagnostic",toJson (diagnostic dep))]
          edges := edges.push row
          unless available || diagnostic dep do missing := missing.push row
  let report := Json.mkObj [("status",toJson "ACTUAL_METADATA_PREFLIGHT_ONLY"),
    ("native_modules",toJson modules.size),("native_actual_physical_roots",Json.arr roots),
    ("old_public_actual_physical_roots",Json.arr oldRoots),
    ("all_project_type_whole_value_edges",Json.arr edges),
    ("ordinary_missing_edges",Json.arr missing),("actual_public_name_collisions",Json.arr collisions),
    ("kernel_replay_or_fullExpr_export",toJson false),("formal_root_filters",toJson (0 : Nat))]
  IO.FS.writeFile outFile report.pretty
  IO.println s!"ACTUAL_CALLEE_PREFLIGHT modules={modules.size} newPhysical={roots.size} oldPhysical={oldRoots.size} edges={edges.size} missingOrdinary={missing.size} collisionObservations={collisions.size}"
  pure 0
