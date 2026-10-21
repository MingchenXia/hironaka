import Lean
import TranscendentalNakamaye.Pending.MaximalContact
import Hironaka.MarkedIdeal.MaximalOrderDefinition
open Lean
run_cmd do
  let env ← getEnv
  let rec nameTree : Name → Json
    | .anonymous => Json.arr #[toJson "anonymous"]
    | .str p s => Json.arr #[toJson "str",nameTree p,toJson s]
    | .num p k => Json.arr #[toJson "num",nameTree p,toJson k]
  let rec binders (e : Expr) : Array Json := Id.run do
    match e with
    | .forallE n t b _ =>
      return #[Json.mkObj [("constructor",toJson "forall"),("name",toJson n.toString),
        ("exact_name_tree",nameTree n)]] ++ binders t ++ binders b
    | .lam n t b _ =>
      return #[Json.mkObj [("constructor",toJson "lambda"),("name",toJson n.toString),
        ("exact_name_tree",nameTree n)]] ++ binders t ++ binders b
    | .letE n t v b _ =>
      return #[Json.mkObj [("constructor",toJson "let"),("name",toJson n.toString),
        ("exact_name_tree",nameTree n)]] ++ binders t ++ binders v ++ binders b
    | .app f a => return binders f ++ binders a
    | .mdata _ b | .proj _ _ b => return binders b
    | _ => return #[]
  let mut rows : Array Json := #[]
  for name in #[`TranscendentalNakamaye.Pending.MaximalContact.IsMaximalOrder,
      `Hironaka.MaximalContact.IsMaximalOrder] do
    let some ci := env.find? name | throwError "Missing actual definition {name}"
    unless ci matches .defnInfo _ do throwError "Not an actual definition {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing actual module owner {name}"
    let some value := ci.value? (allowOpaque := true) | throwError "Missing actual whole value {name}"
    let mut moduleDataOwners : Array String := #[]
    for j in [:env.header.moduleNames.size] do
      if (env.header.moduleData[j]!.constants.any fun c => c.name==name) then
        moduleDataOwners := moduleDataOwners.push env.header.moduleNames[j]!.toString
    rows := rows.push (Json.mkObj [
      ("actual_callee",toJson name.toString),
      ("actual_lookup_owner",toJson env.header.moduleNames[idx.toNat]!.toString),
      ("actual_moduleData_owners",toJson moduleDataOwners),
      ("kind",toJson "definition"),
      ("whole_value_present",toJson true),
      ("type_binders",Json.arr (binders ci.type)),
      ("value_binders",Json.arr (binders value))])
  IO.FS.writeFile "audit/canonical-elementary-family-and-local-producers-20261021/actual-maximal-order-binder-owners.json"
    (Json.arr rows).pretty
  logInfo "ACTUAL_MAXIMAL_ORDER_BINDER_OWNER_WITNESS 2; no name or numeric rewrite"
