import Hironaka
import TranscendentalNakamaye.Pending.HironakaSmoothCentreNearbyIdeal
import TranscendentalNakamaye.Pending.HironakaSmoothCentreNearbyStalks
import TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainActualAmbientHS
import TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainOriginalStalkFreeness
import TranscendentalNakamaye.Pending.RestrictEmptyTower
import Lean
open Lean

private def namespaceRules : List (Name × Name) := [(`TranscendentalNakamaye.FirstPass.NonKahlerLocus, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI2, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI3, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI4, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI, `Hironaka), (`TranscendentalNakamaye.Pending, `Hironaka), (`TranscendentalNakamaye.FirstPass, `Hironaka), (`TranscendentalNakamaye.Upstream, `Hironaka), (`TranscendentalNakamaye, `Hironaka)]
private def renameNamespace (n : Name) : Name := Id.run do
  for (a,b) in namespaceRules do
    if a.isPrefixOf n then return n.replacePrefix a b
  return n
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`TranscendentalNakamaye.Pending.HironakaSmoothCentreNearbyIdeal, `TranscendentalNakamaye.Pending.HironakaSmoothCentreNearbyStalks, `TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainActualAmbientHS, `TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainOriginalStalkFreeness, `TranscendentalNakamaye.Pending.RestrictEmptyTower]
  let mut rows : Array Json := #[]
  for m in targets do
    let some i := env.header.moduleNames.findIdx? (· == m) | throwError "Missing {m}"
    let mut clashes : Array String := #[]
    for ci in env.header.moduleData[i]!.constants do
      unless (privateToUserName? ci.name).isSome do
        if env.contains (renameNamespace ci.name) then clashes := clashes.push ci.name.toString
    rows := rows.push (Json.mkObj [("module",toJson m.toString),("actual_roots",toJson env.header.moduleData[i]!.constants.size),("existing_nonprivate_public_clashes",toJson clashes)])
  IO.FS.writeFile "audit/noncompact-whole-curve-histories-and-prefix-good-20261018/whole-parent-public-name-clashes.json" (Json.pretty (toJson rows))
  logInfo m!"CHECKED_WHOLE_PARENT_CANONICAL_PUBLIC_NAMES {rows.size}"
