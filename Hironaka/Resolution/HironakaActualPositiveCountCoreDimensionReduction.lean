import Hironaka.Resolution.HironakaActualInitialGeneralCoreComparison

/-! Genuine arbitrary-carrier-dimension positive-count CORE reduction.
Actual source geometry displays the smaller lower domain before future
histories; actual native core cuts derive WHOLE lower-core centre cuts. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPositiveCountCoreDimensionReduction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneMaskTower StepOneCanonicalTail
  HironakaActualPositiveCoreCountPresentation HironakaActualInitialCountCoreComparison
  HironakaActualRecursiveCoreValues HironakaStageCenters CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

private theorem projected_fixed_reference
    (hn : 0<n) (k s : ℕ) (J : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y)
    {A B : CMfd.{u} n} (L : MarkedIdeal n A) (S : BlowupTower A B) (p : B)
    (hNative : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y=
      toLex (s, (((invFamily hn (k+1)).inv L S p : ValTy (k+1)) : WithTop (ValTy (k+1))))) :
    stepOneCoreInv hn k J T y=
      toLex (s, ((coreInv hn (k+1) L S p : ValTy (k+1)) : WithTop (ValTy (k+1)))) := by
  unfold stepOneCoreInv
  rw [hNative]
  rfl

/-- Arbitrary source carrier dimension gives the ACTUAL fixed lower core
value after genuine smaller-domain/test geometry, without any lower IH. -/
theorem actual_positive_count_core_reference
    (hn : 0<n) (k d : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain (d+1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (s : ℕ) (a : X)
    (ha : a∈(barMarked J).cosupp) (hLevel : level J (.refl : BlowupTower X X) a=s+1)
    (hNotSpecial : ¬IsSpecial J (.refl : BlowupTower X X) a) :
    let W := lowerMask J (s+1) (.refl : BlowupTower X X) a
    let L := lowerMarked J (s+1) (.refl : BlowupTower X X) a
    a∈W ∧ IsInvDomain d L ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
        StageCentres (fun S C=>∀c∈C,s+1≤level J S c) T →
          IsGeoTestTower L (restrict W T) ∧
          (geoTransformAlong L (restrict W T)).cosupp=
            (Subtype.val : openPreimage T W → Y) ⁻¹'
              {y | y∈(geoTransformAlong (barMarked J) T).cosupp ∧ level J T y=s+1} ∧
          ∀ p∈(geoTransformAlong L (restrict W T)).cosupp,
            stepOneCoreInv hn k J T p=
              toLex (s+1, ((coreInv hn (k+1) L (restrict W T) p : ValTy (k+1)) :
                WithTop (ValTy (k+1)))) := by
  dsimp only
  obtain ⟨hW,hL,hFuture⟩ := actual_positive_count_whole_presentation
    hn J hJ hMax (.refl : BlowupTower X X) trivial s a ha hLevel hNotSpecial
  refine ⟨hW,hL,?_⟩
  intro Y T hT hCuts
  have hT' : IsGeoTestTower (barMarked J) ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hT
  have hCuts' : StageCentres
      (fun S C=>∀c∈C,s+1≤level J ((.refl : BlowupTower X X).append S) c) T := by
    simpa only [BlowupTower.refl_append] using hCuts
  obtain ⟨hTL,_hCurrent,hCos,_hBorn⟩ := hFuture T hT' hCuts'
  simp only [BlowupTower.refl_append] at hCos
  refine ⟨hTL,hCos,?_⟩
  intro p hp
  have hpCount : level J T p=s+1 := by
    rw [hCos] at hp
    exact hp.2
  have hNative := actual_initial_positive_count_native_reference (invFamily hn (k+1))
    J hJ.isWellFormed hJ.one_le_d hMax s a hLevel T hT p hpCount
  exact projected_fixed_reference hn k (s+1) J T p _ _ _ hNative

private theorem step_core_cuts_count
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (s : ℕ) (value : ValTy (k+1)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun S C=>∀c∈C,toLex (s+1,(value : WithTop (ValTy (k+1))))≤
        stepOneCoreInv hn k J S c) T →
      StageCentres (fun S C=>∀c∈C,s+1≤level J S c) T
  | _, .refl, _ => trivial
  | _, .step S C π hπ, hCuts => by
      refine ⟨step_core_cuts_count hn k J s value S hCuts.1,?_⟩
      intro c hc
      have h := hCuts.2 c hc
      change toLex (s+1,_)≤toLex (_,_) at h
      have hFirst : (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J S c)).1=
          level J S c := Seq.StepOneValueMasked.stepOneInvL_fst _ J _ S c
      rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h,_⟩
      · simpa only [hFirst] using h.le
      · simpa only [hFirst] using h.le

/-- Only ACTUAL native whole-centre cuts produce a genuine smaller
analytic lower TEST and WHOLE actual recursive lower-core cuts. -/
theorem actual_positive_count_core_dimension_reduction
    (hn : 0<n) (k d : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain (d+1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (s : ℕ) (a : X)
    (ha : a∈(barMarked J).cosupp) (hLevel : level J (.refl : BlowupTower X X) a=s+1)
    (hNotSpecial : ¬IsSpecial J (.refl : BlowupTower X X) a) (value : ValTy (k+1)) :
    let W := lowerMask J (s+1) (.refl : BlowupTower X X) a
    let L := lowerMarked J (s+1) (.refl : BlowupTower X X) a
    IsInvDomain d L ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
        StageCentres (fun S C=>∀c∈C,toLex (s+1,(value : WithTop (ValTy (k+1))))≤
          stepOneCoreInv hn k J S c) T →
        IsGeoTestTower L (restrict W T) ∧
        StageCentres (fun S C=>∀c∈C,value≤coreInv hn (k+1) L S c) (restrict W T) ∧
        {p | p∈(geoTransformAlong L (restrict W T)).cosupp ∧ value≤coreInv hn (k+1) L (restrict W T) p}=
          (Subtype.val : openPreimage T W → Y) ⁻¹'
            {y | y∈(geoTransformAlong (barMarked J) T).cosupp ∧
              toLex (s+1,(value : WithTop (ValTy (k+1))))≤stepOneCoreInv hn k J T y} := by
  dsimp only
  let W := lowerMask J (s+1) (.refl : BlowupTower X X) a
  let L := lowerMarked J (s+1) (.refl : BlowupTower X X) a
  obtain ⟨_hW,hL,hFuture⟩ := actual_positive_count_core_reference
    hn k d J hJ hMax s a ha hLevel hNotSpecial
  refine ⟨hL,?_⟩
  have hLowerCuts : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
      StageCentres (fun S C=>∀c∈C,toLex (s+1,(value : WithTop (ValTy (k+1))))≤
        stepOneCoreInv hn k J S c) T →
      StageCentres (fun S C=>∀c∈C,value≤coreInv hn (k+1) L S c) (restrict W T) := by
    intro Y T
    induction T with
    | refl => intro _ _; trivial
    | @step Y Z S C π hπ ih =>
      intro hT hCuts
      have hCount := step_core_cuts_count hn k J s value (.step S C π hπ) hCuts
      obtain ⟨hTL,_hCos,_hValues⟩ := hFuture (.step S C π hπ) hT hCount
      obtain ⟨_hSL,_hCosS,hValuesS⟩ := hFuture S hT.1 hCount.1
      refine ⟨ih hT.1 hCuts.1,?_⟩
      intro p hp
      have hpCos : p∈(geoTransformAlong L (restrict W S)).cosupp := hTL.2.2.1 hp
      have hCut := hCuts.2 p hp
      rw [hValuesS p hpCos,Prod.Lex.toLex_le_toLex] at hCut
      simpa only [lt_self_iff_false,true_and,false_or,WithTop.coe_le_coe] using hCut
  intro Y T hT hCuts
  have hCount := step_core_cuts_count hn k J s value T hCuts
  obtain ⟨hTL,hCos,hValues⟩ := hFuture T hT hCount
  refine ⟨hTL,hLowerCuts T hT hCuts,?_⟩
  ext p
  constructor
  · rintro ⟨hp,hLower⟩
    have hpParent : (p : Y)∈(geoTransformAlong (barMarked J) T).cosupp := by
      rw [hCos] at hp
      exact hp.1
    refine ⟨hpParent,?_⟩
    rw [hValues p hp,Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl,WithTop.coe_le_coe.mpr hLower⟩
  · rintro ⟨hpParent,hCut⟩
    have hUpper := StepOneCanonicalTail.level_le_of_mem_lowerMask J
      (fun H hH=>hJ.isWellFormed.isSNCDivisor.1 H hH) (.refl : BlowupTower X X) T hLevel p.2
    simp only [BlowupTower.refl_append] at hUpper
    have hLower : s+1≤level J T p := by
      have h := hCut
      change toLex (s+1,_)≤toLex (_,_) at h
      have hFirst : (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T p)).1=
          level J T p := Seq.StepOneValueMasked.stepOneInvL_fst _ J _ T p
      rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h,_⟩
      · simpa only [hFirst] using h.le
      · simpa only [hFirst] using h.le
    have hpCos : p∈(geoTransformAlong L (restrict W T)).cosupp := by
      rw [hCos]
      exact ⟨hpParent,hUpper.antisymm hLower⟩
    refine ⟨hpCos,?_⟩
    rw [hValues p hpCos,Prod.Lex.toLex_le_toLex] at hCut
    simpa only [lt_self_iff_false,true_and,false_or,WithTop.coe_le_coe] using hCut

end
end Hironaka.HironakaActualPositiveCountCoreDimensionReduction
