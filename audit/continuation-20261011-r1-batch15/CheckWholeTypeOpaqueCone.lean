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
  let roots : List Name := [`Hironaka.Resolution.HironakaSmoothSubmersionMonomialOrdering, `Hironaka.Resolution.HironakaStepOneMemberHeadIncidence, `Hironaka.Resolution.HironakaNormalCrossingsOrderedMonomialTail, `Hironaka.Resolution.HironakaStepOneMemberAcrossMaskValues, `Hironaka.Invariant.StepOneLowerValueExact, `Hironaka.Invariant.StepOneSeqLowerValueExact, `Hironaka.Invariant.MonomialGammaAlongUnivExact, `Hironaka.Invariant.DivisorExponentAlongUnivExact]
  let mut loadedNames := ""
  for m in env.header.moduleNames do
    loadedNames := loadedNames ++ m.toString ++ "\n"
  let mut info : Std.HashMap Name ConstantInfo := {}
  let mut moduleFor : Std.HashMap Name Name := {}
  let mut pending : List Name := []
  let mut rootNames : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m == `Hironaka.Pending.RelativePrincipalization || m == `Hironaka.Pending.EmbeddedResolution then
      throwError m!"Protected module loaded: {m}"
    for ci in env.header.moduleData[i]!.constants do
      info := info.insert ci.name ci
      moduleFor := moduleFor.insert ci.name m
      if roots.contains m then
        pending := ci.name :: pending
        rootNames := rootNames.push ci.name
  let mut visited : NameSet := {}
  let mut project : Array Name := #[]
  let mut edgeCount : Nat := 0
  while !pending.isEmpty do
    let c := pending.head!
    pending := pending.tail!
    if visited.contains c then continue
    visited := visited.insert c
    let cs := c.toString
    if cs.contains "Pending.RelativePrincipalization." || cs.contains "Pending.EmbeddedResolution." ||
        (cs.contains "Kahler" && cs != "Hironaka.FirstPass.NonKahlerLocus.singularLocus") ||
        cs.contains "ThetaPsh" || cs.contains "PositiveCurrent" || cs.contains "RestrictedMass" || cs.contains "ChernWeil" then
      throwError "Forbidden actual proof/type dependency {c}"
    if roots.contains (moduleFor.getD c .anonymous) || ([`AllMasks, `Descent, `Leading, `AnalyticValues, `CurveValues, `Transport, `BoundaryModels, `ExtendedValues, `RegimeDraft, `HistoricalMaskedDraft, `ZeroLevel, `FullMasks, `Gluing, `AmbientThresholds, `GeneralValues, `WholeDraft, `OpenDraft, `OverlapDraft, `FiniteDraft, `ValuesDraft, `MonomialDraft, `WholeSpecialDraft, `SpecialDraft, `CanonicalDraft, `OrderDraft, `HistoricalDraft, `CompanionDraft, `CurveDraft, `Draft] : List Name).contains (moduleFor.getD c .anonymous) || (`Hironaka).isPrefixOf (moduleFor.getD c .anonymous) then
      project := project.push c
    if let some ci := info.get? c then
      let ds := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
      for d in ds do
        pending := d :: pending
        if (roots.contains (moduleFor.getD c .anonymous) || ([`AllMasks, `Descent, `Leading, `AnalyticValues, `CurveValues, `Transport, `BoundaryModels, `ExtendedValues, `RegimeDraft, `HistoricalMaskedDraft, `ZeroLevel, `FullMasks, `Gluing, `AmbientThresholds, `GeneralValues, `WholeDraft, `OpenDraft, `OverlapDraft, `FiniteDraft, `ValuesDraft, `MonomialDraft, `WholeSpecialDraft, `SpecialDraft, `CanonicalDraft, `OrderDraft, `HistoricalDraft, `CompanionDraft, `CurveDraft, `Draft] : List Name).contains (moduleFor.getD c .anonymous) || (`Hironaka).isPrefixOf (moduleFor.getD c .anonymous)) &&
            (roots.contains (moduleFor.getD d .anonymous) || ([`AllMasks, `Descent, `Leading, `AnalyticValues, `CurveValues, `Transport, `BoundaryModels, `ExtendedValues, `RegimeDraft, `HistoricalMaskedDraft, `ZeroLevel, `FullMasks, `Gluing, `AmbientThresholds, `GeneralValues, `WholeDraft, `OpenDraft, `OverlapDraft, `FiniteDraft, `ValuesDraft, `MonomialDraft, `WholeSpecialDraft, `SpecialDraft, `CanonicalDraft, `OrderDraft, `HistoricalDraft, `CompanionDraft, `CurveDraft, `Draft] : List Name).contains (moduleFor.getD d .anonymous) || (`Hironaka).isPrefixOf (moduleFor.getD d .anonymous)) then
          edgeCount := edgeCount + 1
  let out := "/workspace/hironaka/audit/continuation-20261011-r1-batch15/whole-cone-"
  IO.FS.writeFile (out ++ "loaded-modules.txt") loadedNames
  IO.FS.writeFile (out ++ "loaded-module-counts.txt") s!"loaded_modules={env.header.moduleNames.size}\nprotected_modules=0\n"
  logInfo m!"Actual loaded modules {env.header.moduleNames.size}; protected 0"
  let mut rows := ""
  for c in project.qsort Name.lt do
    if (moduleFor.getD c .anonymous) == `Hironaka.Pending.RelativePrincipalization ||
        (moduleFor.getD c .anonymous) == `Hironaka.Pending.EmbeddedResolution then
      throwError m!"Protected proof dependency {c}"
    let cs := c.toString
    if (cs.contains "Kahler" && cs != "Hironaka.FirstPass.NonKahlerLocus.singularLocus") ||
        cs.contains "ThetaPsh" || cs.contains "PositiveCurrent" || cs.contains "RestrictedMass" ||
        cs.contains "ChernWeil" then
      throwError m!"Forbidden metric or project dependency {c}"
    let ci := (info.get? c).get!
    let axs ← liftCoreM <| collectAxioms c
    for a in axs do
      unless [`propext, `Classical.choice, `Quot.sound].contains a do
        throwError m!"Unexpected axiom {a} in actual kernel dependency {c}"
    let bodyCount := ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
    rows := rows ++ s!"{c}\t{moduleFor.getD c .anonymous}\t{bodyCount.size}\n"
  IO.FS.writeFile (out ++ "kernel-constants.tsv") rows
  IO.FS.writeFile (out ++ "compiled-roots.txt") (String.intercalate "\n" (rootNames.qsort Name.lt |>.toList.map Name.toString))
  IO.FS.writeFile (out ++ "cone-counts.txt") s!"compiled_roots={rootNames.size}\nall_constants={visited.size}\nproject_constants={project.size}\nproject_edges={edgeCount}\n"
  logInfo m!"Actual moduleData type/proof dependency audit: {project.size} project constants"
