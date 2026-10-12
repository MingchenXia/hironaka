import Hironaka
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless (`Hironaka).isPrefixOf env.header.moduleNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      if ci.name.isInternalDetail then continue
      let axs ← liftCoreM <| collectAxioms ci.name
      for ax in axs do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError m!"Nonstandard axiom {ax} in {ci.name}"
      logInfo m!"{ci.name}: {axs}"
      count := count + 1
  logInfo m!"All library non-internal mathematical declarations: {count}"
