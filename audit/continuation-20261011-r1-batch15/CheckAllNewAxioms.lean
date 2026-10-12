import Hironaka.Resolution.HironakaSmoothSubmersionMonomialOrdering
import Hironaka.Resolution.HironakaStepOneMemberHeadIncidence
import Hironaka.Resolution.HironakaNormalCrossingsOrderedMonomialTail
import Hironaka.Resolution.HironakaStepOneMemberAcrossMaskValues
import Hironaka.Invariant.StepOneLowerValueExact
import Hironaka.Invariant.StepOneSeqLowerValueExact
import Hironaka.Invariant.MonomialGammaAlongUnivExact
import Hironaka.Invariant.DivisorExponentAlongUnivExact
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`Hironaka.Resolution.HironakaSmoothSubmersionMonomialOrdering, `Hironaka.Resolution.HironakaStepOneMemberHeadIncidence, `Hironaka.Resolution.HironakaNormalCrossingsOrderedMonomialTail, `Hironaka.Resolution.HironakaStepOneMemberAcrossMaskValues, `Hironaka.Invariant.StepOneLowerValueExact, `Hironaka.Invariant.StepOneSeqLowerValueExact, `Hironaka.Invariant.MonomialGammaAlongUnivExact, `Hironaka.Invariant.DivisorExponentAlongUnivExact]
  let mut roots : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    if modules.contains env.header.moduleNames[i]! then
      for ci in env.header.moduleData[i]!.constants do
        roots := roots.push ci.name
        elabCommand (← `(command| #print axioms $(mkIdent ci.name)))
        let axs ← liftCoreM <| collectAxioms ci.name
        for a in axs do
          unless [`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Unexpected actual root axiom {a} in {ci.name}"
  IO.FS.writeFile "/workspace/hironaka/audit/continuation-20261011-r1-batch15/literal-roots.txt" (String.intercalate "\n" (roots.qsort Name.lt |>.toList.map Name.toString))
  logInfo m!"ALL native actual moduleData roots {roots.size}; full literal+collect standard"
