import Lean
import TranscendentalNakamaye.Pending.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealCoherence
open Lean
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (oldName,newName) in #[
    (`TranscendentalNakamaye.Pending.DerivativeIdeal.isCoherent_derivIdeal,
      `Hironaka.DerivativeIdeal.isCoherent_derivIdeal),
    (`TranscendentalNakamaye.Pending.DerivativeIdeal.isCoherent_iterDerivIdeal,
      `Hironaka.DerivativeIdeal.isCoherent_iterDerivIdeal)] do
    for name in #[oldName,newName] do
      let some ci := env.find? name | throwError "Missing actual callee {name}"
      let some idx := env.getModuleIdxFor? name | throwError "No actual module owner {name}"
      let mut binders : Array String := #[]
      let rec names (e : Expr) : Array String := Id.run do
        match e with
        | .forallE n t b _ | .lam n t b _ => return #[n.toString] ++ names t ++ names b
        | .letE n t v b _ => return #[n.toString] ++ names t ++ names v ++ names b
        | .app f a => return names f ++ names a
        | .mdata _ b | .proj _ _ b => return names b
        | _ => return #[]
      binders := names ci.type
      rows := rows.push (Json.mkObj [("name",toJson name.toString),
        ("actual_module",toJson env.header.moduleNames[idx.toNat]!.toString),
        ("type_binders",toJson binders),
        ("whole_value_present",toJson (ci.value? (allowOpaque:=true)).isSome)])
  IO.FS.writeFile "audit/canonical-elementary-family-and-local-producers-20261021/actual-derivative-coherence-owner.json" (Json.arr rows).pretty
