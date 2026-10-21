import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let folder := "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/"
  let lines ← IO.FS.lines (folder ++ "core-new-modules.tsv")
  let targets := lines.map fun s => ((s.splitOn "\t").head!).toName
  let env ← importModules (targets.map fun m => {module := m}) {}
  let mut rows : Array Json := #[]
  let mut total : Nat := 0
  for m in targets do
    let some i := env.header.moduleNames.findIdx? (· == m) | throw (IO.userError s!"Missing {m}")
    let roots := env.header.moduleData[i]!.constants.map fun ci =>
      Json.mkObj [("actual_name",toJson ci.name.toString),
        ("is_private",toJson (privateToUserName? ci.name).isSome)]
    rows := rows.push (Json.mkObj [("module",toJson m.toString),("actual_roots",Json.arr roots)])
    total := total+roots.size
  IO.FS.writeFile (folder ++ "new-public-actual-name-inventory.json") (Json.pretty (Json.arr rows))
  IO.println s!"ALL_NEW_PUBLIC_ACTUAL_NAMES {targets.size} MODULES {total} ROOTS; no kernel or axiom replay"
