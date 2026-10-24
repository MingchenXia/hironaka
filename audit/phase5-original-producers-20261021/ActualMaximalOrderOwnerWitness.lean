import Lean
import Hironaka.Resolution.HironakaActualZeroCoordinateContactSeed
import TranscendentalNakamaye.Pending.MaximalContact

open Lean
set_option maxHeartbeats 0

private partial def binderNames : Expr → Array Name
  | .app f a => binderNames f ++ binderNames a
  | .lam n t b _ => #[n] ++ binderNames t ++ binderNames b
  | .forallE n t b _ => #[n] ++ binderNames t ++ binderNames b
  | .letE n t v b _ => #[n] ++ binderNames t ++ binderNames v ++ binderNames b
  | .mdata _ b => binderNames b
  | .proj _ _ b => binderNames b
  | _ => #[]

run_cmd do
  let env ← getEnv
  let targets : Array (Name × Name) := #[
    (`TranscendentalNakamaye.Pending.MaximalContact,
      `TranscendentalNakamaye.Pending.MaximalContact.IsMaximalOrder),
    (`Hironaka.MarkedIdeal.MaximalOrderDefinition, `Hironaka.MaximalContact.IsMaximalOrder)]
  let mut rows : Array Json := #[]
  for (module, name) in targets do
    let some idx := env.header.moduleNames.findIdx? (· == module)
      | throwError "Missing actual definition owner {module}"
    let actual := env.header.moduleData[idx]!.constants.filter (·.name == name)
    unless actual.size == 1 do throwError "Expected exactly one own physical definition {module}/{name}"
    let ci := actual[0]!
    unless ci matches .defnInfo _ do throwError "Expected actual definition {name}"
    let some value := ci.value? (allowOpaque := true)
      | throwError "Missing actual whole definition {name}"
    let resolved := env.getModuleIdxFor? name
    unless resolved == some idx do throwError "Environment owner differs from physical owner {name}"
    rows := rows.push (Json.mkObj [
      ("actual_physical_moduleData_owner", toJson module.toString),
      ("actual_name", toJson name.toString),
      ("kind", toJson "definition"),
      ("whole_value_present", toJson true),
      ("actual_own_type_binders", toJson ((binderNames ci.type).map Name.toString)),
      ("actual_own_value_binders", toJson ((binderNames value).map Name.toString))])
  let result := Json.mkObj [
    ("status", toJson "PASS_TWO_ACTUAL_PHYSICAL_CALLEE_DEFINITION_OWNERS"),
    ("old_whole_module_or_Expr_replay", toJson false),
    ("names_suffixes_or_proof_fields_erased", toJson false),
    ("rows", Json.arr rows)]
  IO.FS.writeFile "audit/phase5-original-producers-20261021/actual-maximal-order-owner-witness.json" result.pretty
  logInfo "PASS_ACTUAL_MAXIMAL_ORDER_DEFINITION_OWNERS"
