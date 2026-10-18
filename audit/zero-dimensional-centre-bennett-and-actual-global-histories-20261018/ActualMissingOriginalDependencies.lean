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
  let path := "audit/zero-dimensional-centre-bennett-and-actual-global-histories-20261018/frozen-major-extraction-plan.json"
  let plan ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let strings ← IO.ofExcept (plan.getObjValAs? (Array String) "source_modules")
  let targets := strings.map String.toName
  let mut privateCopies : NameSet := {}
  for i in [0:env.header.moduleNames.size] do
    unless (`Hironaka).isPrefixOf env.header.moduleNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      if let some user := privateToUserName? ci.name then
        privateCopies := privateCopies.insert user
  let mut used : NameSet := {}
  for m in targets do
    let some i := env.header.moduleNames.findIdx? (· == m) | throwError "Missing {m}"
    for ci in env.header.moduleData[i]!.constants do
      for n in ci.type.getUsedConstants do used := used.insert n
      for n in ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] do
        used := used.insert n
  let mut missing : Array Json := #[]
  for name in used.toArray do
    let some i := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[i.toNat]!
    unless (`TranscendentalNakamaye).isPrefixOf owner do continue
    if targets.contains owner then continue
    let user := (privateToUserName? name).getD name
    let canonical := renameNamespace user
    if env.contains canonical || privateCopies.contains canonical then continue
    missing := missing.push (Json.mkObj [("name",toJson name.toString),("owner",toJson owner.toString),("canonical_user_name",toJson canonical.toString)])
  IO.FS.writeFile "audit/zero-dimensional-centre-bennett-and-actual-global-histories-20261018/actual-missing-original-dependencies.json" (Json.pretty (toJson missing))
  logInfo m!"ACTUAL_MISSING_ORIGINAL_DEPENDENCIES {missing.size}; ALL49_ROOTS_COMPLETE_TYPES_AND_VALUES_INSPECTED"
