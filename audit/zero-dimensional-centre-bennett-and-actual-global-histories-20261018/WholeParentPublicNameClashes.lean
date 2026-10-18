import Hironaka
import TranscendentalNakamaye.Pending.HironakaActualAnalyticPointInitialRestriction
import TranscendentalNakamaye.Pending.HironakaActualAxisContraction
import TranscendentalNakamaye.Pending.HironakaActualAxisSpecializationHS
import TranscendentalNakamaye.Pending.HironakaActualFlatCoordinateIntrinsicHS
import TranscendentalNakamaye.Pending.HironakaActualOpenCoordinateStrictSquare
import TranscendentalNakamaye.Pending.HironakaActualOriginalDerivativeSheaf
import TranscendentalNakamaye.Pending.HironakaActualPointBlowupCoordinates
import TranscendentalNakamaye.Pending.HironakaActualPointBlowupExceptionalLocus
import TranscendentalNakamaye.Pending.HironakaActualPointCentreStrictGenerators
import TranscendentalNakamaye.Pending.HironakaActualPointDehomogenizedInitial
import TranscendentalNakamaye.Pending.HironakaActualPointExceptionalInitialForm
import TranscendentalNakamaye.Pending.HironakaActualPointExceptionalVanishing
import TranscendentalNakamaye.Pending.HironakaActualPointGeometricBennett
import TranscendentalNakamaye.Pending.HironakaActualPointInitialIdealInclusion
import TranscendentalNakamaye.Pending.HironakaActualPointNormalizedBennett
import TranscendentalNakamaye.Pending.HironakaActualPointUnitCoordinateChange
import TranscendentalNakamaye.Pending.HironakaActualUnshiftedInitialHSTransfer
import TranscendentalNakamaye.Pending.HironakaActualVanishingIntrinsicHSTransport
import TranscendentalNakamaye.Pending.HironakaActualZeroDimensionalCentreBennett
import TranscendentalNakamaye.Pending.HironakaOriginalCurveFullLocality
import TranscendentalNakamaye.Pending.HironakaOriginalCurveFullRebase
import TranscendentalNakamaye.Pending.HironakaOriginalCurveLocalReferenceComparison
import TranscendentalNakamaye.Pending.HironakaOriginalCurveLowerReferenceRebase
import TranscendentalNakamaye.Pending.HironakaOriginalCurveTangentChange
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteCutFixedLowerValues
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteCutPositiveLowerValues
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteFullCutSmoothHistory
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteOrderCutBoundTwoSmoothValues
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteOrderCutCompanionTests
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteOrderCutMiddleHistory
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteOrderCutRebase
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteOrderCutSmoothCompanions
import TranscendentalNakamaye.Pending.HironakaOriginalFiniteStepOneCutMiddleHistory
import TranscendentalNakamaye.Pending.HironakaOriginalPositiveCurveLowerComparison
import TranscendentalNakamaye.Pending.HironakaOriginalZeroCurveLowerComparison
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveExactTerminalRepadding
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveGlobalPrefixTowers
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveGlobalSuccessorBlowup
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveGlobalSuccessorCentre
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveGlobalSuccessorCentreIdeal
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveGlobalSuccessorGeometry
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveGlobalSuccessorMap
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveLocalStationaryCentres
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveStoppedAtlasTransition
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveStoppedPrefixOpenNaturality
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveStoppedStageTerminalRanges
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveSuccessorLocalBlowup
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveUniformInitialStage
import TranscendentalNakamaye.Pending.HironakaSharpActualCurveUniformSuccessorRestriction
import Lean
open Lean

private def namespaceRules : List (Name × Name) := [(`TranscendentalNakamaye.FirstPass.NonKahlerLocus, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI2, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI3, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI4, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI, `Hironaka), (`TranscendentalNakamaye.Pending, `Hironaka), (`TranscendentalNakamaye.FirstPass, `Hironaka), (`TranscendentalNakamaye.Upstream, `Hironaka), (`TranscendentalNakamaye, `Hironaka)]
private def renameNamespace (n : Name) : Name := Id.run do
  for (a,b) in namespaceRules do
    if a.isPrefixOf n then return n.replacePrefix a b
  return n
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`TranscendentalNakamaye.Pending.HironakaActualFormalStandardMonomialHS, `TranscendentalNakamaye.Pending.HironakaActualHomogeneousInitialHS, `TranscendentalNakamaye.Pending.HironakaActualFiniteInitialGeneration, `TranscendentalNakamaye.Pending.HironakaActualHolomorphicFibreHS, `TranscendentalNakamaye.Pending.HironakaActualCoordinateSpecializationHS, `TranscendentalNakamaye.Pending.HironakaActualTranslatedInitialHS, `TranscendentalNakamaye.Pending.HironakaActualWholeStalkHolomorphicPullback, `TranscendentalNakamaye.Pending.HironakaActualBiholomorphicWholeStalkHS, `TranscendentalNakamaye.Pending.HironakaActualOpenIntrinsicHS, `TranscendentalNakamaye.Pending.HironakaActualBlowupOffCentreIntrinsicHS, `TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainActualAmbientHS]
  let mut rows : Array Json := #[]
  for m in targets do
    let some i := env.header.moduleNames.findIdx? (· == m) | throwError "Missing {m}"
    let mut clashes : Array String := #[]
    for ci in env.header.moduleData[i]!.constants do
      unless (privateToUserName? ci.name).isSome do
        if env.contains (renameNamespace ci.name) then clashes := clashes.push ci.name.toString
    rows := rows.push (Json.mkObj [("module",toJson m.toString),("actual_roots",toJson env.header.moduleData[i]!.constants.size),("existing_nonprivate_public_clashes",toJson clashes)])
  IO.FS.writeFile "audit/zero-dimensional-centre-bennett-and-actual-global-histories-20261018/whole-parent-public-name-clashes.json" (Json.pretty (toJson rows))
  logInfo m!"CHECKED_WHOLE_PARENT_CANONICAL_PUBLIC_NAMES {rows.size}"
