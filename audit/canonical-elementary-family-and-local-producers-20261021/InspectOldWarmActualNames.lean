import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let path := "/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021/"
  let targets := (← IO.FS.lines (path ++ "old-warm-modules-snapshot.txt")).map String.toName
  let env ← importModules (targets.map fun m => {module := m}) {}
  let mut rows : Array Json := #[]
  let mut total := 0
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`Hironaka).isPrefixOf m do continue
    let roots := env.header.moduleData[i]!.constants.map (fun ci => toJson ci.name.toString)
    rows := rows.push (Json.mkObj [("module",toJson m.toString),("actual_roots",Json.arr roots)])
    total := total + roots.size
  IO.FS.writeFile (path ++ "old-warm-actual-name-inventory.json") (Json.pretty (Json.arr rows))
  IO.println s!"OLD_ACTUAL_METADATA_NAME_INVENTORY {rows.size} MODULES {total} ROOTS; no kernel/axiom replay"
