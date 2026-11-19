import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualPhaseMap
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterInitialBound

/-! The SAME computed outer successors in the actual equal-profile branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualNext
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalIntrinsicHSSuperlevels OriginalNativeHSShadowOuterState
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeHSCurrentSmoothContext
  OriginalNativeHSCurrentEqualPhaseContext OriginalNativeCurrentTerminalSmoothPhaseMap
  OriginalNativeHSCurrentEqualPhaseMap OriginalNativeSmoothComposition
  HironakaG11VanishingWindows HironakaG11PresReduction HironakaG11CompatibleCanonicalTowers
  HironakaActualPowerBoundaryExponents HironakaG1NativeFiniteProductState

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T) (hKS : IsCompact KS) (hKT : IsCompact KT)
  (hnS : (singularShadow S).Nonempty) (hnT : (singularShadow T).Nonempty)

private theorem sourceSing (hne : (singularShadow S).Nonempty) : (shadow S ∩ intrinsicSingularLocus S.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hne
private theorem targetSing (hne : (singularShadow T).Nonempty) : (shadow T ∩ intrinsicSingularLocus T.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hne
private theorem targetExtra : KT ⊆ (⊤ : Opens Y.obj.left) := by simp
private theorem sourceExtraContains : KS ⊆ sourceExtra c hKT hnT := by
  intro z hz
  exact OriginalNativeHSCurrentPhaseRestriction.contains T c.targetOpen c.targetCompactClosure c.targetRange
    c.targetContains hKT hnT ⊤ targetExtra (c.compactImage ⟨z,hz,rfl⟩)

local notation "ES" => sourceExtra c hKT hnT
local notation "hES" => sourceExtraContains c hKT hnT
local notation "HT" => OriginalNativeHSFactoryTerminalFrame.profile T.source (shadow T) (shadow_compact T hKT) (targetSing hnT)
local notation "HS" => OriginalNativeHSFactoryTerminalFrame.profile S.source (shadow S) (shadow_compact S hKS) (sourceSing hnS)
local notation "wS" => OriginalNativeHSCurrentPhaseRestriction.phaseWindow S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "wT" => OriginalNativeHSCurrentPhaseRestriction.phaseWindow T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "rS" => OriginalNativeHSCurrentPhaseRestriction.phaseRawRecord S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "rT" => OriginalNativeHSCurrentPhaseRestriction.phaseRawRecord T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "tS" => OriginalNativeHSCurrentPhaseRestriction.phaseStage S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "tT" => OriginalNativeHSCurrentPhaseRestriction.phaseStage T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "xS" => OriginalNativeHSCurrentPhaseRestriction.phaseNativeStage S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "xT" => OriginalNativeHSCurrentPhaseRestriction.phaseNativeStage T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "eS" => OriginalNativeHSFactoryTerminalFrame.exponent S.source (shadow S) (shadow_compact S hKS) (sourceSing hnS)
local notation "eT" => OriginalNativeHSFactoryTerminalFrame.exponent T.source (shadow T) (shadow_compact T hKT) (targetSing hnT)
local notation "dS" => OriginalNativeHSFactoryTerminalFrame.dimension S.source (shadow S) (shadow_compact S hKS) (sourceSing hnS)
local notation "dT" => OriginalNativeHSFactoryTerminalFrame.dimension T.source (shadow T) (shadow_compact T hKT) (targetSing hnT)


/-- The factory source profile is literally the actual outer-run profile. -/
theorem source_factory_profile_eq_outer : HS =
    OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S) (baseShadow_compact S hKS) hnS := by
  rfl

/-- The factory target profile is literally the actual outer-run profile. -/
theorem target_factory_profile_eq_outer : HT =
    OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hKT) hnT := by
  rfl

local notation "cR" => pastContext c hKS hKT hnS hnT
local notation "VS" => sourceOpen c hKS hKT hnS hnT
local notation "VT" => targetOpen c hKT hnT
local notation "hVS" => OriginalNativeHSCurrentPhaseRestriction.compactClosure S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "hVT" => OriginalNativeHSCurrentPhaseRestriction.compactClosure T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "rangeS" => OriginalNativeHSCurrentPhaseRestriction.closure_nextRange S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "rangeT" => OriginalNativeHSCurrentPhaseRestriction.closure_nextRange T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "nextS" => OriginalNativeHSShadowOuterRun.next S hKS hnS
local notation "nextT" => OriginalNativeHSShadowOuterRun.next T hKT hnT
local notation "isoS" => OriginalNativeHSCurrentPhaseRestriction.comparison S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "isoT" => OriginalNativeHSCurrentPhaseRestriction.comparison T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "oldHistS" => Context.sourceHistory (pastContext c hKS hKT hnS hnT)
local notation "oldHistT" => Context.targetHistory (pastContext c hKS hKT hnS hnT)
local notation "newHistS" => OriginalNativeHSCurrentOverlap.history nextS VS hVS rangeS
local notation "newHistT" => OriginalNativeHSCurrentOverlap.history nextT VT hVT rangeT
local notation "outerS" => OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S) (baseShadow_compact S hKS) hnS
local notation "outerT" => OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hKT) hnT

/-- The actual unique arrow between the two computed phase endpoints. -/
def phaseMap (hEq : outerS = finiteProductHS r outerT) : (xS).Y ⟶ (xT).Y :=
  Classical.choose (exists_unique_equal_phase_map c hKS hKT hnS hnT hEq)

theorem phaseMap_smooth (hEq : outerS = finiteProductHS r outerT) : IsSmoothMorphism (phaseMap c hKS hKT hnS hnT hEq) :=
  (Classical.choose_spec (exists_unique_equal_phase_map c hKS hKT hnS hnT hEq)).1.1

theorem phaseMap_square (hEq : outerS = finiteProductHS r outerT) :
    phaseMap c hKS hKT hnS hnT hEq ≫ (xT).q = (xS).q ≫ (cR).map :=
  (Classical.choose_spec (exists_unique_equal_phase_map c hKS hKT hnS hnT hEq)).1.2

/-- The actual map between the same computed next endpoints. -/
def nextMap (hEq : outerS = finiteProductHS r outerT) :=
  (isoS).inv ≫ phaseMap c hKS hKT hnS hnT hEq ≫ (isoT).hom

theorem nextMap_smooth (hEq : outerS = finiteProductHS r outerT) : IsSmoothMorphism (nextMap c hKS hKT hnS hnT hEq) := by
  have hs : LocallyRingedSpace.IsOpenImmersion (isoS).inv.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (isoS)).inv
    infer_instance
  have ht : LocallyRingedSpace.IsOpenImmersion (isoT).hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (isoT)).hom
    infer_instance
  exact isSmoothMorphism_comp _ _ (isSmoothMorphism_of_isOpenImmersion _ hs)
    (isSmoothMorphism_comp _ _ (phaseMap_smooth c hKS hKT hnS hnT hEq) (isSmoothMorphism_of_isOpenImmersion _ ht))

theorem nextMap_original_square (hEq : outerS = finiteProductHS r outerT) :
    nextMap c hKS hKT hnS hnT hEq ≫ (newHistT).projection ≫ (cR).targetBaseInclusion =
      (newHistS).projection ≫ (cR).sourceBaseInclusion ≫ f := by
  have hs0 : (isoS).hom ≫ (newHistS).projection = (xS).q ≫ (oldHistS).projection :=
    OriginalNativeHSCurrentPhaseRestriction.comparison_projection S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
  have ht0 : (isoT).hom ≫ (newHistT).projection = (xT).q ≫ (oldHistT).projection :=
    OriginalNativeHSCurrentPhaseRestriction.comparison_projection T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
  have hs : (isoS).inv ≫ (xS).q ≫ (oldHistS).projection = (newHistS).projection := by
    have h := congrArg (fun p => (isoS).inv ≫ p) hs0
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  change ((isoS).inv ≫ phaseMap c hKS hKT hnS hnT hEq ≫ (isoT).hom) ≫ (newHistT).projection ≫ (cR).targetBaseInclusion = _
  calc
    _ = (isoS).inv ≫ phaseMap c hKS hKT hnS hnT hEq ≫ ((isoT).hom ≫ (newHistT).projection) ≫ (cR).targetBaseInclusion := by simp only [Category.assoc]
    _ = (isoS).inv ≫ (phaseMap c hKS hKT hnS hnT hEq ≫ (xT).q) ≫ (oldHistT).projection ≫ (cR).targetBaseInclusion := by rw [ht0]; simp only [Category.assoc]
    _ = (isoS).inv ≫ ((xS).q ≫ (cR).map) ≫ (oldHistT).projection ≫ (cR).targetBaseInclusion := by rw [phaseMap_square]
    _ = (isoS).inv ≫ (xS).q ≫ ((cR).map ≫ (cR).targetHistory.projection ≫ (cR).targetBaseInclusion) := by simp only [Category.assoc]
    _ = (isoS).inv ≫ (xS).q ≫ ((cR).sourceHistory.projection ≫ (cR).sourceBaseInclusion ≫ f) := by rw [(cR).square]
    _ = ((isoS).inv ≫ (xS).q ≫ (oldHistS).projection) ≫ (cR).sourceBaseInclusion ≫ f := by simp only [Category.assoc]
    _ = _ := by rw [hs]

/-- Actual smooth Context on the SAME two computed outer successors. -/
def nextContext (hEq : outerS = finiteProductHS r outerT) : Context f e0 r O a ha hChart nextS nextT where
  compactImage := c.compactImage
  sourceOpen := VS
  sourceCompactClosure := hVS
  sourceContains := OriginalNativeHSCurrentPhaseRestriction.contains S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
  sourceRange := rangeS
  sourceChartRange := (cR).sourceChartRange
  targetOpen := VT
  targetCompactClosure := hVT
  targetContains := OriginalNativeHSCurrentPhaseRestriction.contains T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
  targetRange := rangeT
  imageClosure := (cR).imageClosure
  map := nextMap c hKS hKT hnS hnT hEq
  smooth := nextMap_smooth c hKS hKT hnS hnT hEq
  square := nextMap_original_square c hKS hKT hnS hnT hEq

/-- The whole closure of the new source open stays in the old source open. -/
theorem source_closure_subset_old (hEq : outerS = finiteProductHS r outerT) :
    closure ((nextContext c hKS hKT hnS hnT hEq).sourceOpen : Set X.obj.left) ⊆ c.sourceOpen :=
  OriginalNativeHSCurrentPhaseRestriction.closure_subset_old S c.sourceOpen c.sourceCompactClosure c.sourceRange
    c.sourceContains hKS hnS ES hES

/-- The whole closure of the new target open stays in the old target open. -/
theorem target_closure_subset_old (hEq : outerS = finiteProductHS r outerT) :
    closure ((nextContext c hKS hKT hnS hnT hEq).targetOpen : Set Y.obj.left) ⊆ c.targetOpen :=
  OriginalNativeHSCurrentPhaseRestriction.closure_subset_old T c.targetOpen c.targetCompactClosure c.targetRange
    c.targetContains hKT hnT ⊤ targetExtra

/-- The SAME computed successors have a genuine smooth Context, shrinking both old opens. -/
theorem exists_context (hEq : outerS = finiteProductHS r outerT) :
    ∃ d : Context f e0 r O a ha hChart nextS nextT,
      d.sourceOpen ≤ c.sourceOpen ∧ d.targetOpen ≤ c.targetOpen :=
  ⟨nextContext c hKS hKT hnS hnT hEq,
    fun _ h => source_closure_subset_old c hKS hKT hnS hnT hEq (subset_closure h),
    fun _ h => target_closure_subset_old c hKS hKT hnS hnT hEq (subset_closure h)⟩
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualNext
