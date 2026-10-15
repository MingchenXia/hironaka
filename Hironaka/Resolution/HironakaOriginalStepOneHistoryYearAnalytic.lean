/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.StepOneDropExact
import Hironaka.Resolution.HironakaOriginalFrozenRecursiveLower
/-! True global lower-history year thresholds of the SAME original masked StepOne
regime, retaining actual special resets. Source-first complete blueprint precedes
code. Full arbitrary recursive lower superlevels and scheduler remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOneHistoryYearAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HomogenizedIdealAlong StepOneValue StepOneLowerDomain StepOneRegime CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

/-- The real previous higher-level or equal-level special reset locus. -/
def stepOneSpecialResetLocus (m : MarkedIdeal n X) (T : BlowupTower X Y) (s : ℕ) : Set Y :=
  {y | y ∈ (geoTransformAlong m T).cosupp ∧
    (s < level m T y ∨ (s=level m T y ∧ IsSpecial m T y))}

/-- Only original data construct actual global current coefficient/boundary baselines. -/
theorem isComplexAnalyticSubset_stepOneHistoryBaseline (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) (s : ℕ) :
    IsComplexAnalyticSubset (n := n) {y | y ∈ (geoTransformAlong m T).cosupp ∧ s ≤ level m T y} := by
  have hB := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hB.2.1
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d
  exact hA.inter (HironakaBoundaryCountAnalyticSuperlevels.isComplexAnalyticSubset_stepOne_level_superlevel
    hn m h.isWellFormed T hB.1 s)

/-- True original special-top equations present EXACTLY the whole reset locus. -/
theorem isComplexAnalyticSubset_stepOneSpecialResetLocus (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) (s : ℕ) :
    IsComplexAnalyticSubset (n := n) (stepOneSpecialResetLocus m T s) := by
  have hB := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hc
  have heq : stepOneSpecialResetLocus m T s =
      {y | y ∈ (geoTransformAlong (barMarked m) T).cosupp ∧
        toLex (s,(⊤ : WithTop (ValTy k))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m T y} := by
    ext y
    constructor
    · rintro ⟨hy,hreset⟩
      have hybar : y ∈ (geoTransformAlong (barMarked m) T).cosupp := by rwa [hB.2.2]
      exact ⟨hybar,(HironakaStepOneSpecialAnalyticLoci.stepOneInvM_top_threshold_iff
        (invFamily hn k) hn m h.isWellFormed h.one_le_d hmax T hB.1 hybar s).mpr hreset⟩
    · rintro ⟨hy,hvalue⟩
      exact ⟨by rwa [← hB.2.2],(HironakaStepOneSpecialAnalyticLoci.stepOneInvM_top_threshold_iff
        (invFamily hn k) hn m h.isWellFormed h.one_le_d hmax T hB.1 hy s).mp hvalue⟩
  rw [heq]
  exact HironakaStepOneSpecialAnalyticLoci.isComplexAnalyticSubset_stepOneInvM_top_superlevel
    (invFamily hn k) hn m h.isWellFormed h.one_le_d hmax T hB.1 s

/-- Genuine original successor drop implies inherited cosupport and level nonincrease. -/
theorem canonical_step_cosupport_and_level_le (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) (.step T C π hπ))
    (z : Z) (hz : z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp) :
    π z ∈ (geoTransformAlong m T).cosupp ∧ level m (.step T C π hπ) z ≤ level m T (π z) := by
  have hd := StepOneSeq.stepDrop_stepOneInvM (k := k+1) (invFamily hn k) h hmax hn T C π hπ hc z hz
  have hv : Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m (.step T C π hπ) z ≤
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m T (π z) := by
    by_cases hC : π z ∈ C
    · exact (hd.2.1 hC).le
    · exact (hd.2.2 hC).le
  have hl := Prod.Lex.le_iff.mp hv
  rw [Seq.StepOneValueMasked.stepOneInvL_fst,Seq.StepOneValueMasked.stepOneInvL_fst] at hl
  exact ⟨hd.1,hl.elim (fun h => h.le) (fun h => h.1.le)⟩

private theorem reset_iff_not_regime (m : MarkedIdeal n X) (T : BlowupTower X Y) (s : ℕ)
    (y : Y) (hy : y ∈ (geoTransformAlong m T).cosupp) (hs : s ≤ level m T y) :
    y ∈ stepOneSpecialResetLocus m T s ↔ ¬ stepRegime m s T y := by
  constructor
  · rintro ⟨_,hlt | ⟨he,hsp⟩⟩ hreg
    · have := hreg.1; omega
    · exact hreg.2 hsp
  · intro hnot
    refine ⟨hy,?_⟩
    by_cases hlt : s < level m T y
    · exact Or.inl hlt
    · have he : s=level m T y := by omega
      exact Or.inr ⟨he,by by_contra hsp; exact hnot ⟨he.symm,hsp⟩⟩

/-- The literal actual masked lower starting-year bound, with its whole baseline. -/
def stepOneHistoryYearSuperlevel (m : MarkedIdeal n X) (T : BlowupTower X Y) (s r : ℕ) : Set Y :=
  {y | y ∈ (geoTransformAlong m T).cosupp ∧ s ≤ level m T y ∧
    regimeRun (stepRegime m s) T y ≤ r}

/-- Exact whole zero-run equation, including genuine old special resets. -/
theorem stepOneHistoryYearSuperlevel_step_zero (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) (.step T C π hπ)) (s : ℕ) :
    stepOneHistoryYearSuperlevel m (.step T C π hπ) s 0 =
      {z | z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp ∧ s ≤ level m (.step T C π hπ) z} ∩
        π ⁻¹' stepOneSpecialResetLocus m T s := by
  classical
  ext z
  constructor
  · intro hz
    have hp := canonical_step_cosupport_and_level_le hn m h hmax T C π hπ hc z hz.1
    refine ⟨⟨hz.1,hz.2.1⟩,(reset_iff_not_regime m T s (π z) hp.1 (hz.2.1.trans hp.2)).mpr ?_⟩
    intro hg
    have hrun := regimeRun_step_of (stepRegime m s) T C π hπ hg
    have hle := hz.2.2
    rw [hrun] at hle
    omega
  · intro hz
    have hp := canonical_step_cosupport_and_level_le hn m h hmax T C π hπ hc z hz.1.1
    have hnot := (reset_iff_not_regime m T s (π z) hp.1 (hz.1.2.trans hp.2)).mp hz.2
    refine ⟨hz.1.1,hz.1.2,?_⟩
    rw [regimeRun_step_of_not (stepRegime m s) T C π hπ hnot]

/-- Exact whole successor equation on the actual original finite history. -/
theorem stepOneHistoryYearSuperlevel_step_succ (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) (.step T C π hπ)) (s r : ℕ) :
    stepOneHistoryYearSuperlevel m (.step T C π hπ) s (r+1) =
      {z | z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp ∧ s ≤ level m (.step T C π hπ) z} ∩
        π ⁻¹' (stepOneSpecialResetLocus m T s ∪ stepOneHistoryYearSuperlevel m T s r) := by
  classical
  ext z
  constructor
  · intro hz
    have hp := canonical_step_cosupport_and_level_le hn m h hmax T C π hπ hc z hz.1
    refine ⟨⟨hz.1,hz.2.1⟩,?_⟩
    by_cases hg : stepRegime m s T (π z)
    · right
      have hle := hz.2.2
      rw [regimeRun_step_of (stepRegime m s) T C π hπ hg] at hle
      exact ⟨hp.1,hz.2.1.trans hp.2,by omega⟩
    · left
      exact (reset_iff_not_regime m T s (π z) hp.1 (hz.2.1.trans hp.2)).mpr hg
  · intro hz
    have hp := canonical_step_cosupport_and_level_le hn m h hmax T C π hπ hc z hz.1.1
    refine ⟨hz.1.1,hz.1.2,?_⟩
    rcases hz.2 with hreset | hyear
    · have hnot := (reset_iff_not_regime m T s (π z) hp.1 (hz.1.2.trans hp.2)).mp hreset
      rw [regimeRun_step_of_not (stepRegime m s) T C π hπ hnot]
      exact Nat.zero_le _
    · by_cases hg : stepRegime m s T (π z)
      · rw [regimeRun_step_of (stepRegime m s) T C π hπ hg]
        exact Nat.succ_le_succ hyear.2.2
      · rw [regimeRun_step_of_not (stepRegime m s) T C π hπ hg]
        exact Nat.zero_le _

/-- Only original inputs construct genuine GLOBAL history-year equations by
actual finite unions/intersections and true holomorphic blowup pullbacks. -/
theorem isComplexAnalyticSubset_stepOneHistoryYearSuperlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d) :
    ∀ {A : CMfd.{u} n} (T : BlowupTower X A),
      IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T →
      ∀ s r : ℕ,IsComplexAnalyticSubset (n := n) (stepOneHistoryYearSuperlevel m T s r)
  | _,.refl,hc,s,r => by
    have heq : stepOneHistoryYearSuperlevel m (.refl : BlowupTower X X) s r =
        {z | z ∈ (geoTransformAlong m (.refl : BlowupTower X X)).cosupp ∧ s ≤ level m .refl z} := by
      ext z
      simp [stepOneHistoryYearSuperlevel,regimeRun_refl]
    rw [heq]
    exact isComplexAnalyticSubset_stepOneHistoryBaseline hn m h hmax .refl hc s
  | _,.step T C π hπ,hc,s,r => by
    have hbase := isComplexAnalyticSubset_stepOneHistoryBaseline hn m h hmax (.step T C π hπ) hc s
    have hreset := isComplexAnalyticSubset_stepOneSpecialResetLocus hn m h hmax T hc.1 s
    cases r with
    | zero =>
      rw [stepOneHistoryYearSuperlevel_step_zero hn m h hmax T C π hπ hc s]
      exact hbase.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hreset)
    | succ r =>
      have hold := isComplexAnalyticSubset_stepOneHistoryYearSuperlevel hn m h hmax T hc.1 s r
      rw [stepOneHistoryYearSuperlevel_step_succ hn m h hmax T C π hπ hc s r]
      exact hbase.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff
        (HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hreset hold))

/-- An original positive full history internally constructs the genuine entire
companion lower-history year analytic consumer, with no selected companion input. -/
theorem isComplexAnalyticSubset_actual_frozen_companion_lower_history_year (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp)
    (hq : 1 ≤ HironakaOriginalFrozenCompanionPresentation.orderAt m T x) (s r : ℕ) :
    IsComplexAnalyticSubset (n := n)
      (stepOneHistoryYearSuperlevel (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
        (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x) s r) := by
  obtain ⟨_,hK,hmax,hcanK,_⟩ :=
    HironakaOriginalFrozenCompanionPresentation.actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  exact isComplexAnalyticSubset_stepOneHistoryYearSuperlevel hn _ hK hmax _ hcanK s r

end
end Hironaka.HironakaOriginalStepOneHistoryYearAnalytic
