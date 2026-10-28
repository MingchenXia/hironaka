import Hironaka.Resolution.HironakaDisjointAnalyticSaturatedGluing
import Lean.Util.CollectAxioms

open Lean
run_cmd do
  let env := (← getEnv).setExporting false
  setEnv env
  let target := `Hironaka.Resolution.HironakaDisjointAnalyticSaturatedGluing
  let some idx := env.header.moduleNames.findIdx? (· == target)
    | throwError "Missing actual module {target}"
  let roots := env.header.moduleData[idx]!.constants
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut cache : NameMap (Array Name) := {}
  let mut rows : Array Json := #[]
  for ci in roots do
    let value := ci.value? (allowOpaque := true)
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless value.isSome do throwError "Missing whole physical-CI body {ci.name}"
    | _ => pure ()
    let mut direct : NameSet := {}
    for dep in ci.type.getUsedConstants do direct := direct.insert dep
    if let some v := value then
      for dep in v.getUsedConstants do direct := direct.insert dep
    if let .inductInfo info := ci then
      for ctor in info.ctors do direct := direct.insert ctor
    let mut axioms : NameSet := {}
    if let .axiomInfo info := ci then
      unless allowed.contains ci.name do throwError "Nonstandard physical axiom {ci.name}"
      let some (.axiomInfo checked) := env.checked.get.find? ci.name
        | throwError "No checked standard axiom {ci.name}"
      unless info.type.equal checked.type do throwError "Different physical axiom type {ci.name}"
      axioms := axioms.insert ci.name
    for dep in direct.toArray do
      let axs ← if let some cached := cache.find? dep then pure cached else do
        unless ((env.setExporting false).find? dep).isSome do
          throwError "Missing actual dependency {dep} of {ci.name}"
        let axs ← collectAxioms dep
        cache := cache.insert dep axs
        pure axs
      for ax in axs do
        unless allowed.contains ax do throwError "Nonstandard axiom {ax} through {dep} in {ci.name}"
        axioms := axioms.insert ax
    let axs := axioms.toArray.map Name.toString
    rows := rows.push (Json.mkObj [("name",toJson ci.name.toString),
      ("axioms",toJson axs),("own_type_callees",toJson ci.type.getUsedConstants.size),("type_callee_names",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("own_value_callees",toJson ((value.map Expr.getUsedConstants).getD #[]).size),("value_callee_names",toJson (((value.map Expr.getUsedConstants).getD #[]).map Name.toString))])
    logInfo m!"ACTUAL_PHYSICAL_ROOT {ci.name} AXIOMS {repr axs}"
  let out := "/workspace/hironaka-phase5-main-integration/audit/disjoint-producers-20261028/independent/physical-07.json"
  IO.FS.writeFile out ((Json.mkObj [("module",toJson target.toString),
    ("actual_root_count",toJson roots.size),("roots",Json.arr rows)]).pretty)
  logInfo m!"ALL_ACTUAL_PHYSICAL_ROOTS {roots.size} allowed axioms only"
