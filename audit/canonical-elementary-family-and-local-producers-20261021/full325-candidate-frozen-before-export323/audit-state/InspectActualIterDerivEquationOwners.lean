import Lean
import TranscendentalNakamaye.Pending.HironakaNormalCrossingsDoubleLocusMarkedCompatibility
import Hironaka.Resolution.HironakaNormalCrossingsDoubleLocusMarkedCompatibility
open Lean
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for idx in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[idx]!
    for ci in env.header.moduleData[idx]!.constants do
      let name := ci.name.toString
      unless (name.splitOn ".HolomorphicTaylorTail.iterDeriv").length > 1 do continue
      let actualOwner := match env.getModuleIdxFor? ci.name with
        | some j => env.header.moduleNames[j.toNat]!.toString
        | none => "NO_IMPORTED_MODULE_OWNER"
      let kind := match ci with
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      rows := rows.push (Json.mkObj [
        ("actual_name",toJson name),
        ("moduleData_owner",toJson owner.toString),
        ("actual_lookup_owner",toJson actualOwner),
        ("kind",toJson kind),
        ("whole_value_present",toJson (ci.value? (allowOpaque := true)).isSome)])
  IO.FS.writeFile "audit/canonical-elementary-family-and-local-producers-20261021/actual-iterDeriv-equation-owners.json"
    (Json.arr rows).pretty
  logInfo m!"ACTUAL_ITERDERIV_EQUATION_OWNER_ROWS {rows.size}"
