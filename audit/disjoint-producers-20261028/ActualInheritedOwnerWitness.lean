import Lean
open Lean
private def nameTree : Name → Json
  | .anonymous => toJson ([toJson "anonymous"] : List Json)
  | .str p s => toJson [toJson "str",nameTree p,toJson s]
  | .num p k => toJson [toJson "num",nameTree p,toJson k]
private partial def binders (e : Expr) : Array Json :=
  match e with
  | .forallE n t b _ | .lam n t b _ =>
    #[Json.mkObj [("name",toJson n.toString),("exact_name_tree",nameTree n)]] ++ binders t ++ binders b
  | .letE n t v b _ =>
    #[Json.mkObj [("name",toJson n.toString),("exact_name_tree",nameTree n)]] ++ binders t ++ binders v ++ binders b
  | .app f a => binders f ++ binders a
  | .mdata _ b | .proj _ _ b => binders b
  | _ => #[]
def main (args : List String) : IO UInt32 := do
  let [out] := args | throw (IO.userError "Expected output path")
  initSearchPath (← findSysroot)
  let modules := #[`TranscendentalNakamaye.Pending.DerivativeIdeal,
    `Hironaka.MarkedIdeal.DerivativeIdealCoherence,
    `TranscendentalNakamaye.Pending.MaximalContact,
    `Hironaka.MarkedIdeal.MaximalOrderDefinition,
    `TranscendentalNakamaye.Pending.HironakaDisjointControlledNormalPivot,
    `Hironaka.Resolution.HironakaDisjointControlledNormalPivot]
  let env := (← importModules (modules.map fun m => {module := m}) {}).setExporting false
  let names := #[`TranscendentalNakamaye.Pending.DerivativeIdeal.derivFamily,
    `TranscendentalNakamaye.Pending.DerivativeIdeal.derivIdeal_mem_iff_of_generators,
    `Hironaka.DerivativeIdeal.derivFamily,
    `Hironaka.DerivativeIdeal.derivIdeal_mem_iff_of_generators,
    `TranscendentalNakamaye.Pending.MaximalContact.IsMaximalOrder,
    `Hironaka.MaximalContact.IsMaximalOrder,
    `TranscendentalNakamaye.Pending.BlowupControlledTransform.controlledTransform.congr_simp,
    `Hironaka.BlowupControlledTransform.controlledTransform.congr_simp]
  let mut rows := #[]
  for name in names do
    let some ci := env.find? name | throw (IO.userError s!"Missing actual witness {name}")
    let mut owners : Array String := #[]
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleData[i]!.constants.any (·.name == name) then
        owners := owners.push env.header.moduleNames[i]!.toString
    let lookup := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => "<not-imported>"
    rows := rows.push (Json.mkObj [("actual_name",toJson name.toString),
      ("all_actual_physical_owners",toJson owners),("actual_lookup_owner",toJson lookup),
      ("actual_type_binders",toJson (binders ci.type)),
      ("actual_whole_value_binders",toJson ((ci.value? (allowOpaque := true)).map binders)),
      ("actual_type_used_constants",toJson (ci.type.getUsedConstants.map Name.toString))])
  IO.FS.writeFile out (Json.arr rows).pretty
  IO.println s!"ACTUAL_OWNER_AND_BINDER_WITNESSES {rows.size} no kernel/Expr replay"
  pure 0
