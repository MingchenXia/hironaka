import Hironaka.Resolution.HironakaRelativeNormalStandardMonomials
import Hironaka.Resolution.HironakaRelativeNormalUniformLocalization
import Hironaka.Resolution.HironakaStepOneMemberMaskedMonomialValues
import Hironaka.Resolution.HironakaNormalCrossingsFiniteMarkedCompletion
import Hironaka.MarkedIdeal.GeoStrictEmptyExact
import Hironaka.MarkedIdeal.GeoResolutionAppendExact
import Hironaka.Invariant.UnitCosupportExact
import Hironaka.Invariant.NonzeroAlongUnivExact
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List Name := [`Hironaka.Resolution.HironakaRelativeNormalStandardMonomials, `Hironaka.Resolution.HironakaRelativeNormalUniformLocalization, `Hironaka.Resolution.HironakaStepOneMemberMaskedMonomialValues, `Hironaka.Resolution.HironakaNormalCrossingsFiniteMarkedCompletion, `Hironaka.MarkedIdeal.GeoStrictEmptyExact, `Hironaka.MarkedIdeal.GeoResolutionAppendExact, `Hironaka.Invariant.UnitCosupportExact, `Hironaka.Invariant.NonzeroAlongUnivExact]
  let mut count : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless roots.contains env.header.moduleNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      let axioms ← liftCoreM <| collectAxioms ci.name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError m!"Unexpected axiom {ax} in {ci.name}"
      logInfo m!"{ci.name}: {axioms}"
      count := count + 1
  logInfo m!"All actual new moduleData constants: {count}"
