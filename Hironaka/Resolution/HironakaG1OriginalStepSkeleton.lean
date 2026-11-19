import Hironaka.Resolution.HironakaG8MemberLoci
import Hironaka.Invariant.StepOneSeq

/-! The original Step 1 skeleton is shared by weakly equivalent marked
records, even when their marks differ. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalStepSkeleton
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq StepOneValue StepOneRegime HomogenizedIdealAlong
  HironakaG11InvBMClass HironakaG8MemberLoci

/-- Equal boundaries and weak equivalence identify the original Step 1
level, special branch, and each level's regime at a common test stage. -/
theorem original_step_skeleton_of_wEquiv
    {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : A.N = B.N)
    (hW : WEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T) (y : Y) :
    level A T y = level B T y ∧ (IsSpecial A T y ↔ IsSpecial B T y) ∧
      ∀ s, stepRegime A s T y ↔ stepRegime B s T y := by
  have hlev := level_eq_of_E_eq hW.1 T y
  have hsp := isSpecial_iff_of_wEquiv hn hA hB hW (SameCarrierDim.of_N_eq hN) T hT y
  refine ⟨hlev,hsp,?_⟩
  intro s
  change (level A T y = s ∧ ¬ IsSpecial A T y) ↔ (level B T y = s ∧ ¬ IsSpecial B T y)
  rw [hlev,hsp]

/-- The same native Step 1 regime has the same literal clock along every
common controlled history. -/
theorem original_step_run_of_wEquiv
    {n kA kB : ℕ} (hn : 0 < n) {X : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : A.N = B.N)
    (hW : WEquiv A B) (s : ℕ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T → ∀ y : Y,
      regimeRun (stepRegime A s) T y = regimeRun (stepRegime B s) T y
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, z => by
    have hT' := ((isGeoTestTower_step_iff A T C π hπ).mp hT).1
    have hiff := (original_step_skeleton_of_wEquiv hn A B hA hB hN hW T hT' (π z)).2.2 s
    rw [regimeRun_step,regimeRun_step,original_step_run_of_wEquiv hn A B hA hB hN hW s T hT' (π z)]
    by_cases hP : stepRegime A s T (π z)
    · rw [if_pos hP,if_pos (hiff.mp hP)]
    · rw [if_neg hP,if_neg (fun h => hP (hiff.mpr h))]

/-- At every special point, the original masked Step 1 values themselves
agree for an arbitrary shared lower invariant, even for unequal marks. -/
theorem original_step_special_value_of_wEquiv
    {n kA kB q : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {Λ : Type} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n q Λ)
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : A.N = B.N)
    (hW : WEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : IsSpecial A T y) :
    Seq.StepOneValueMasked.stepOneInvM R A T y = Seq.StepOneValueMasked.stepOneInvM R B T y := by
  obtain ⟨hlev,hsp,_⟩ := original_step_skeleton_of_wEquiv hn A B hA hB hN hW T hT y
  change Seq.StepOneValueMasked.stepOneInvL R A (StepOneValueMasked.lowerMarkedM A) T y =
    Seq.StepOneValueMasked.stepOneInvL R B (StepOneValueMasked.lowerMarkedM B) T y
  rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R A _ T hy,
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R B _ T (hsp.mp hy),hlev]

/-- When two actual points have different Step 1 levels, their original
Step 1 value comparison is determined by the levels and agrees for any
two records with the same ordered boundary. -/
theorem original_step_distinct_level_cut_iff
    {n q : ℕ} {X Y : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n q Λ)
    (A B : MarkedIdeal n X) (hE : A.E = B.E) (T : BlowupTower X Y) (z w : Y)
    (hne : level A T z ≠ level A T w) :
    Seq.StepOneValueMasked.stepOneInvM R A T z < Seq.StepOneValueMasked.stepOneInvM R A T w ↔
      Seq.StepOneValueMasked.stepOneInvM R B T z < Seq.StepOneValueMasked.stepOneInvM R B T w := by
  have hz := level_eq_of_E_eq hE T z
  have hw := level_eq_of_E_eq hE T w
  rcases lt_or_gt_of_ne hne with h | h
  · have hA : Seq.StepOneValueMasked.stepOneInvM R A T z < Seq.StepOneValueMasked.stepOneInvM R A T w :=
      Seq.StepOneValueMasked.stepOneInvL_lt_of_level_lt R A (StepOneValueMasked.lowerMarkedM A) h
    have hB : Seq.StepOneValueMasked.stepOneInvM R B T z < Seq.StepOneValueMasked.stepOneInvM R B T w :=
      Seq.StepOneValueMasked.stepOneInvL_lt_of_level_lt R B (StepOneValueMasked.lowerMarkedM B) (by simpa only [←hz,←hw] using h)
    exact iff_of_true hA hB
  · have hA : Seq.StepOneValueMasked.stepOneInvM R A T w < Seq.StepOneValueMasked.stepOneInvM R A T z :=
      Seq.StepOneValueMasked.stepOneInvL_lt_of_level_lt R A (StepOneValueMasked.lowerMarkedM A) h
    have hB : Seq.StepOneValueMasked.stepOneInvM R B T w < Seq.StepOneValueMasked.stepOneInvM R B T z :=
      Seq.StepOneValueMasked.stepOneInvL_lt_of_level_lt R B (StepOneValueMasked.lowerMarkedM B) (by simpa only [←hz,←hw] using h)
    exact iff_of_false (not_lt_of_ge hA.le) (not_lt_of_ge hB.le)

private theorem nonspecial_lt_special
    {n k q : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n q Λ)
    (A : MarkedIdeal n X) (hA : IsInvDomain k A) (hmA : IsMaximalOrderAlong A.N A.ideal A.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {z w : Y}
    (hz : z ∈ (geoTransformAlong A T).cosupp) (hzNS : ¬ IsSpecial A T z)
    (hwS : IsSpecial A T w) (hlev : level A T z = level A T w) :
    Seq.StepOneValueMasked.stepOneInvM R A T z < Seq.StepOneValueMasked.stepOneInvM R A T w := by
  have hbar := (StepOneBridge.barMarked_wEquiv A hA).2 T
  have hTB := hbar.1.mpr hT
  have hzB : z ∈ (geoTransformAlong (barMarked A) T).cosupp := (hbar.2 hTB).symm ▸ hz
  have hfinite := Seq.StepOneValueMasked.lowerValueL_ne_top A R hA.isWellFormed hA.one_le_d hn hmA
    (StepOneValueMasked.lowerMarkedM A) T hTB hzB hzNS
  change Seq.StepOneValueMasked.stepOneInvL R A (StepOneValueMasked.lowerMarkedM A) T z <
    Seq.StepOneValueMasked.stepOneInvL R A (StepOneValueMasked.lowerMarkedM A) T w
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R A _ T hzNS,
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R A _ T hwS,Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨hlev,lt_top_iff_ne_top.mpr hfinite⟩

/-- At equal Step 1 levels, if at least one endpoint is special, the full
original Step 1 strict cut is the same on two weakly equivalent records. -/
theorem original_step_special_tie_cut_iff
    {n kA kB q : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n q Λ)
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (hN : A.N = B.N) (hW : WEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (z w : Y) (hz : z ∈ (geoTransformAlong A T).cosupp) (hw : w ∈ (geoTransformAlong A T).cosupp)
    (hlev : level A T z = level A T w) (hspecial : IsSpecial A T z ∨ IsSpecial A T w) :
    Seq.StepOneValueMasked.stepOneInvM R A T z < Seq.StepOneValueMasked.stepOneInvM R A T w ↔
      Seq.StepOneValueMasked.stepOneInvM R B T z < Seq.StepOneValueMasked.stepOneInvM R B T w := by
  have hTB := (hW.2 T).1.mp hT
  have hcos := (hW.2 T).2 hT
  have hzB : z ∈ (geoTransformAlong B T).cosupp := hcos ▸ hz
  have hwB : w ∈ (geoTransformAlong B T).cosupp := hcos ▸ hw
  obtain ⟨hlz,hsz,_⟩ := original_step_skeleton_of_wEquiv hn A B hA hB hN hW T hT z
  obtain ⟨hlw,hsw,_⟩ := original_step_skeleton_of_wEquiv hn A B hA hB hN hW T hT w
  have hlevB : level B T z = level B T w := hlz.symm.trans (hlev.trans hlw)
  by_cases hzS : IsSpecial A T z
  · by_cases hwS : IsSpecial A T w
    · rw [original_step_special_value_of_wEquiv hn R A B hA hB hN hW T hT hzS,
        original_step_special_value_of_wEquiv hn R A B hA hB hN hW T hT hwS]
    · have hAgt := nonspecial_lt_special hn R A hA hmA T hT hw hwS hzS hlev.symm
      have hBgt := nonspecial_lt_special hn R B hB hmB T hTB hwB (fun h => hwS (hsw.mpr h)) (hsz.mp hzS) hlevB.symm
      exact iff_of_false (not_lt_of_ge hAgt.le) (not_lt_of_ge hBgt.le)
  · have hwS : IsSpecial A T w := hspecial.resolve_left hzS
    have hAlt := nonspecial_lt_special hn R A hA hmA T hT hz hzS hwS hlev
    have hBlt := nonspecial_lt_special hn R B hB hmB T hTB hzB (fun h => hzS (hsz.mpr h)) (hsw.mp hwS) hlevB
    exact iff_of_true hAlt hBlt
end
end Hironaka.HironakaG1OriginalStepSkeleton
