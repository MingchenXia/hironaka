import Lean
import TranscendentalNakamaye.Pending.RiemannExtensionThin
import Hironaka.Analytic.RiemannExtensionThin
open Lean
run_cmd do
  let env ← getEnv
  let rec nameTree : Name → Json
    | .anonymous => Json.arr #[toJson "anonymous"]
    | .str p s => Json.arr #[toJson "str",nameTree p,toJson s]
    | .num p k => Json.arr #[toJson "num",nameTree p,toJson k]
  let mut rows : Array Json := #[]
  for module in #[`TranscendentalNakamaye.Pending.RiemannExtensionThin,
      `Hironaka.Analytic.RiemannExtensionThin] do
    let some idx := env.header.moduleNames.findIdx? (· == module)
      | throwError "Missing actual module {module}"
    for ci in env.header.moduleData[idx]!.constants do
      let some user := privateToUserName? ci.name | continue
      unless user.toString.endsWith ".termE" || user.toString.contains "._aux_" do continue
      let some value := ci.value? (allowOpaque := true)
        | throwError "Missing whole generated value {ci.name}"
      let mut quotedNames : Array Json := #[]
      let rec decodeName (e : Expr) : Option Name := do
        if e.isConstOf ``Name.anonymous then return .anonymous
        if e.isAppOfArity ``Name.mkStr 2 then
          let p ← decodeName e.getAppArgs[0]!
          let .lit (.strVal s) := e.getAppArgs[1]! | none
          return .str p s
        if e.isAppOfArity ``Name.mkNum 2 then
          let p ← decodeName e.getAppArgs[0]!
          let some k := e.getAppArgs[1]!.nat? | none
          return .num p k
        none
      let rec visit (e : Expr) (path : String) : StateM (Array Json) Unit := do
        if let some name := decodeName e then
          unless name == .anonymous do
            modify (·.push (Json.mkObj [("path",toJson path),("name",toJson name.toString),("exact_name_tree",nameTree name)]))
            return
        match e with
        | .app f a => visit f (path++"/fn");visit a (path++"/arg")
        | .lam _ t b _ | .forallE _ t b _ => visit t (path++"/type");visit b (path++"/body")
        | .letE _ t v b _ => visit t (path++"/type");visit v (path++"/value");visit b (path++"/body")
        | .mdata _ b => visit b (path++"/metadata-body")
        | .proj _ _ b => visit b (path++"/projection-body")
        | _ => pure ()
      quotedNames := ((visit value "value").run #[]).2
      rows := rows.push (Json.mkObj [("owner",toJson module.toString),("name",toJson ci.name.toString),
        ("user_name",toJson user.toString),("exact_name_tree",nameTree ci.name),("type",toJson (reprStr ci.type)),
        ("is_parser_descriptor",toJson (ci.type.isConstOf ``ParserDescr)),
        ("whole_quoted_names",toJson quotedNames)])
  IO.FS.writeFile
    "audit/analytic-coefficient-dictionary-and-chosen-overlaps-20261015/parser-generated-owner-witness.json" (Json.arr rows).pretty
  logInfo m!"ACTUAL_PARSER_GENERATED_OWNER_WITNESSES {rows.size}"
