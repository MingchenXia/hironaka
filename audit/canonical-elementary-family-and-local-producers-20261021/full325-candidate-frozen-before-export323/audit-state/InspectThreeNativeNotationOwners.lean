import TranscendentalNakamaye.Pending.HironakaActualClosedContactControlledRestriction
import TranscendentalNakamaye.Pending.HironakaActualPrincipalJetMultiplication
import TranscendentalNakamaye.Pending.HironakaActualPrincipalHSFormula
open Lean
run_cmd do
  let env ← getEnv
  let modules := #[`TranscendentalNakamaye.Pending.HironakaActualClosedContactControlledRestriction,
    `TranscendentalNakamaye.Pending.HironakaActualPrincipalJetMultiplication,
    `TranscendentalNakamaye.Pending.HironakaActualPrincipalHSFormula]
  let mut rows : Array Json := #[]
  for m in modules do
    let some i := env.header.moduleNames.findIdx? (· == m) | throwError "Missing {m}"
    let mut count : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      unless ci.type.isConstOf ``ParserDescr || ci.type.isConstOf ``Macro ||
          ci.type.isConstOf ``PrettyPrinter.Unexpander do continue
      let typ := if ci.type.isConstOf ``ParserDescr then "Lean.ParserDescr"
        else if ci.type.isConstOf ``Macro then "Lean.Macro" else "Lean.PrettyPrinter.Unexpander"
      let kind := match ci with | .defnInfo _ => "definition" | _ => "REJECTED_NON_DEFINITION"
      unless kind == "definition" && (ci.value? (allowOpaque := true)).isSome do
        throwError "Missing complete typed generated definition {ci.name}"
      rows := rows.push (Json.mkObj [("actual_owner",toJson m.toString),
        ("actual_name",toJson ci.name.toString),("actual_type",toJson typ),
        ("kind",toJson kind),("whole_value_present",toJson true)])
      count := count+1
    unless count == 6 do throwError "Unexpected exact owner count {m}: {count}"
  IO.FS.writeFile "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/three-native-notation-owner-witness.json" (Json.pretty (Json.arr rows))
  logInfo m!"ACTUAL_THREE_NATIVE_NOTATION_OWNERS {rows.size}; no public classification or structural-equality claim"
