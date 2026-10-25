import Hironaka
import Lean.Util.CollectAxioms

/-! Final-only audit draft. Read each actual moduleData ConstantInfo itself.
Never replace that root payload by collectAxioms ci.name. Transitive callees
still have ordinary Lean Name semantics and use the standard imported cache.
No kernel replay, Expr exporter, root filter, or axiom waiver is implemented. -/
open Lean

namespace Phase5Build08NarrowPhysicalCIAxiomAudit

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let rosterPath := (← IO.getEnv "HIRONAKA_PHYSICAL_CI_ROSTER").getD
    "audit/phase5-original-producers-20261021/new17physical-build08-narrow-modules.txt"
  let outputPath := (← IO.getEnv "HIRONAKA_PHYSICAL_CI_OUTPUT").getD
    "audit/phase5-original-producers-20261021/new17physical-build08-narrow-ci-axioms.json"
  let targets := (← IO.FS.lines rosterPath).map String.toName
  let mut uniqueTargets : NameSet := {}
  for m in targets do
    if uniqueTargets.contains m then throwError "Duplicate source-roster module {m}"
    uniqueTargets := uniqueTargets.insert m
  let actual := env.header.moduleNames.filter fun m => (`Hironaka).isPrefixOf m
  let allPhysical := (← IO.FS.lines "audit/phase5-original-producers-20261021/new17physical-all-source-modules.txt").map String.toName
  unless actual.size == allPhysical.size do
    throwError "Actual imported standalone module count {actual.size} differs from exact physical-source roster {allPhysical.size}"
  for m in actual do
    unless allPhysical.contains m do throwError "Unexpected actual standalone module {m}"
  for m in allPhysical do
    unless actual.contains m do throwError "Source module not actually imported {m}"
  for target in targets do
    unless actual.contains target do throwError "New physical module not actually imported {target}"
  unless targets.size == 3 do throwError "Expected exactly three corrected new physical module owners"

  let mut dependencyCache : NameMap (Array Name) := {}
  let mut rootOwners : NameMap (Array Name) := {}
  let mut duplicateNames : Array Name := #[]
  let mut rows : Array Json := #[]
  let mut modules : Array Json := #[]
  let mut total := 0
  let mut requiredBodies := 0
  let mut actualAxiomRoots := 0
  let mut ownTypeEdges := 0
  let mut ownValueEdges := 0
  let mut constructorEdges := 0
  let mut deduplicatedEdges := 0
  let mut frontendRoots := 0
  for target in targets do
    let some idx := env.header.moduleNames.findIdx? (· == target)
      | throwError "Missing actual standalone module {target}"
    let roots := env.header.moduleData[idx]!.constants
    for ci in roots do
      let previous := (rootOwners.find? ci.name).getD #[]
      if previous.contains target then
        throwError "Repeated actual moduleData root within physical owner {target}: {ci.name}"
      if previous.size == 1 then duplicateNames := duplicateNames.push ci.name
      rootOwners := rootOwners.insert ci.name (previous.push target)

      -- These are the physical CI's OWN expressions, including opaque bodies.
      let value := ci.value? (allowOpaque := true)
      if #["definition", "theorem", "opaque"].contains (kind ci) then
        unless value.isSome do
          throwError "Missing whole physical CI body {ci.name} in {target}; no fallback"
        requiredBodies := requiredBodies + 1
      let typeDeps := ci.type.getUsedConstants
      let valueDeps := (value.map Expr.getUsedConstants).getD #[]
      ownTypeEdges := ownTypeEdges + typeDeps.size
      ownValueEdges := ownValueEdges + valueDeps.size
      let mut direct : NameSet := {}
      for dep in typeDeps do direct := direct.insert dep
      for dep in valueDeps do direct := direct.insert dep
      -- Match the standard collector's inductive→constructor dependency edge.
      if let .inductInfo info := ci then
        for ctor in info.ctors do
          direct := direct.insert ctor
          constructorEdges := constructorEdges + 1

      let mut axs : NameSet := {}
      if let .axiomInfo info := ci then
        actualAxiomRoots := actualAxiomRoots + 1
        unless allowedAxioms.contains ci.name do
          throwError "Nonstandard PHYSICAL axiomInfo root {ci.name} in {target}"
        let some (.axiomInfo standard) := env.checked.get.find? ci.name
          | throwError "Allowed-name physical axiom has no checked standard axiom {ci.name}"
        unless info.type.equal standard.type do
          throwError "Physical allowed-name axiom has a different whole type: {ci.name}"
        axs := axs.insert ci.name

      deduplicatedEdges := deduplicatedEdges + direct.size
      for dep in direct.toArray do
        let mut dependencyAxioms : Array Name := #[]
        if let some cached := dependencyCache.find? dep then
          dependencyAxioms := cached
        else
          unless ((env.setExporting false).find? dep).isSome do
            throwError "Unresolved physical-CI dependency {dep} of {ci.name} in {target}; no fallback"
          let collected ← collectAxioms dep
          for ax in collected do
            unless allowedAxioms.contains ax do
              throwError "Nonstandard transitive axiom {ax} through {dep} in PHYSICAL root {ci.name} owned by {target}"
          dependencyCache := dependencyCache.insert dep collected
          dependencyAxioms := collected
        for ax in dependencyAxioms do axs := axs.insert ax

      let frontend := if ci.type.isConstOf ``Lean.ParserDescr then "Lean.ParserDescr"
        else if ci.type.isConstOf ``Lean.Macro then "Lean.Macro"
        else if ci.type.isConstOf ``Lean.PrettyPrinter.Unexpander then "Lean.PrettyPrinter.Unexpander"
        else ""
      unless frontend.isEmpty do frontendRoots := frontendRoots + 1
      let resolvedOwner := match env.getModuleIdxFor? ci.name with
        | some owner => env.header.moduleNames[owner.toNat]!.toString
        | none => "<no imported module owner>"
      let result := axs.toArray.qsort Name.lt
      rows := rows.push (Json.mkObj [
        ("actual_moduleData_owner", toJson target.toString),
        ("actual_name", toJson ci.name.toString), ("actual_kind", toJson (kind ci)),
        ("own_whole_body_present", toJson value.isSome),
        ("own_type_direct_constants", toJson typeDeps.size),
        ("own_whole_value_direct_constants", toJson valueDeps.size),
        ("deduplicated_direct_callees_including_inductive_constructors", toJson direct.size),
        ("actual_frontend_type", toJson frontend),
        ("environment_Name_resolution_owner", toJson resolvedOwner),
        ("physical_payload_transitive_axioms", toJson (result.map Name.toString))])
      logInfo m!"PHYSICAL_CI_ROOT {target} {ci.name} KIND {kind ci} OWN_AXIOMS {result}"
    modules := modules.push (Json.mkObj [
      ("module", toJson target.toString), ("actual_root_observations", toJson roots.size)])
    total := total + roots.size
    logInfo m!"MODULE_PHYSICAL_CI_ROOTS {target} {roots.size}"

  let mut duplicateRows : Array Json := #[]
  for name in duplicateNames do
    duplicateRows := duplicateRows.push (Json.mkObj [
      ("actual_name", toJson name.toString),
      ("all_physical_moduleData_owners", toJson (((rootOwners.find? name).getD #[]).map Name.toString))])
  let report := Json.mkObj [
    ("status", toJson "PASS_ALL_ACTUAL_PHYSICAL_CI_PAYLOAD_AXIOMS"),
    ("source_roster", toJson rosterPath), ("actual_modules", toJson targets.size),
    ("actual_physical_root_observations", toJson total),
    ("all_imported_standalone_modules", toJson actual.size),
    ("old_payload_audit_reused_without_replay", toJson true),
    ("definition_theorem_opaque_whole_bodies_required", toJson requiredBodies),
    ("actual_axiomInfo_roots_checked", toJson actualAxiomRoots),
    ("all_actual_frontend_roots_retained", toJson frontendRoots),
    ("own_type_direct_constant_edges", toJson ownTypeEdges),
    ("own_whole_value_direct_constant_edges", toJson ownValueEdges),
    ("inductive_constructor_edges", toJson constructorEdges),
    ("per_physical_root_deduplicated_direct_callee_edges", toJson deduplicatedEdges),
    ("duplicate_global_names_with_distinct_physical_owners", Json.arr duplicateRows),
    ("module_counts", Json.arr modules), ("all_physical_root_rows", Json.arr rows),
    ("physical_root_payload_replaced_by_environment_Name_lookup", toJson false),
    ("standard_collectAxioms_used_for_deduplicated_environment_callees", toJson true),
    ("kernel_or_Expr_replay_performed", toJson false),
    ("roots_frontend_or_helpers_filtered", toJson false)]
  IO.FS.writeFile outputPath (Json.pretty report)
  logInfo m!"ALL_PHYSICAL_CI_ROOTS {total} standard axioms only; {targets.size} modules; every own type/value scanned"

end Phase5Build08NarrowPhysicalCIAxiomAudit
