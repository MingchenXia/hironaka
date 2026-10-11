/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDimensionThreeStepOneCurveEnvelope

/-!
# Literal Step 1 head predicates and actual curve history freezing

Actual level and whole top-threshold head loci pull back holomorphically along
literal tails. A true finite analytic predicate family on an actual curve
internally yields a dimension-zero exception; genuine component points outside
it have equal own current levels and identical literal regimeRun. Original
actual domain3 and constructed invFamily3 canonical inputs internally produce
the companion curve and history exception. No fixed-run or compatibility input.
Literal lower member/contact ideal extension and whole General3/G3 remain open.
Blueprint: `hironaka-step-one-curve-history-predicates-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneCurveHistoryPredicates
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneLowerDomain
  HironakaBoundaryCountAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  HironakaCurveAnalyticPredicates GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  CanonicalCentres
open Hironaka

noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual head-level superlevel pulled back along its literal tail. -/
def historyLevelSuperlevel (m : MarkedIdeal n X) (T : BlowupTower X Y) (r s : ℕ) : Set Y :=
  (tail T r).proj ⁻¹' {z | s ≤ level m (head T r) z}

/-- Actual entire head cosupport top threshold pulled back along its literal tail. -/
def historyTopSuperlevel (hn : 0 < n) (m : MarkedIdeal n X) (T : BlowupTower X Y) (r s : ℕ) : Set Y :=
  (tail T r).proj ⁻¹' {z | z ∈ (geoTransformAlong (barMarked m) (head T r)).cosupp ∧
    toLex (s, (⊤ : WithTop (ValTy 2))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m (head T r) z}

/-- Genuine transformed indexed boundary levels and the actual tail produce analytic head predicates. -/
theorem isComplexAnalyticSubset_historyLevelSuperlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) (r s : ℕ) :
    IsComplexAnalyticSubset (n := n) (historyLevelSuperlevel m T r s) := by
  have hh := ((isGeoTestTower_iff_head_tail (barMarked m) T r).mp hT).1
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T r).contMDiff_proj
    (isComplexAnalyticSubset_stepOne_level_superlevel hn m hw (head T r) hh s)

/-- Genuine full Step1 top thresholds and the actual tail produce analytic head predicates. -/
theorem isComplexAnalyticSubset_historyTopSuperlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (hd : 1 ≤ m.d)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) (r s : ℕ) :
    IsComplexAnalyticSubset (n := n) (historyTopSuperlevel hn m T r s) := by
  have hh := ((isGeoTestTower_iff_head_tail (barMarked m) T r).mp hT).1
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T r).contMDiff_proj
    (isComplexAnalyticSubset_stepOneInvM_top_superlevel (invFamily hn 2) hn m hw hd hmax (head T r) hh s)

private theorem mem_head_cosupport_of_current (m : MarkedIdeal n X) (hw : m.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked m) T)
    (r : ℕ) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked m) T).cosupp) :
    (tail T r).proj y ∈ (geoTransformAlong (barMarked m) (head T r)).cosupp := by
  obtain ⟨hh, ht⟩ := (isGeoTestTower_iff_head_tail (barMarked m) T r).mp hT
  have hwH := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked m hw) (head T r) hh
  have hy' : y ∈ (geoTransformAlong (geoTransformAlong (barMarked m) (head T r)) (tail T r)).cosupp := by
    rw [← geoTransformAlong_head_tail]
    exact hy
  exact proj_mem_cosupp_of_mem_cosupp hwH.isClosedSubmanifold_N hwH.isCoherent (tail T r) ht hy'

/-- Actual current support internally projects to the head; its literal regime has this exact dictionary. -/
theorem stepRegime_head_iff_history_predicates (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (hd : 1 ≤ m.d)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) (r s : ℕ)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked m) T).cosupp) :
    stepRegime m s (head T r) ((tail T r).proj y) ↔
      y ∈ historyLevelSuperlevel m T r s ∧ y ∉ historyLevelSuperlevel m T r (s+1) ∧
        y ∉ historyTopSuperlevel hn m T r s := by
  have hyH := mem_head_cosupport_of_current m hw T hT r hy
  have hh := ((isGeoTestTower_iff_head_tail (barMarked m) T r).mp hT).1
  have htop := stepOneInvM_top_threshold_iff (invFamily hn 2) hn m hw hd hmax (head T r) hh hyH s
  change (_ = s ∧ ¬ IsSpecial m (head T r) ((tail T r).proj y)) ↔
    s ≤ level m (head T r) ((tail T r).proj y) ∧
      ¬ s+1 ≤ level m (head T r) ((tail T r).proj y) ∧
      ¬ (_ ∧ toLex (s, (⊤ : WithTop (ValTy 2))) ≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m (head T r) ((tail T r).proj y))
  rw [htop]
  constructor
  · rintro ⟨heq, hnsp⟩
    exact ⟨heq.ge, by omega, fun ht => ht.2.elim (by omega) (fun hs => hnsp hs.2)⟩
  · rintro ⟨hlo, hhi, hnot⟩
    have heq : level m (head T r) ((tail T r).proj y) = s := by omega
    exact ⟨heq, fun hs => hnot ⟨hyH, Or.inr ⟨heq.symm, hs⟩⟩⟩

private theorem level_le_original_length (m : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) :
    level m T y ≤ m.E.length := by
  classical
  show (Finset.univ.filter fun i : Fin (origMembers m T).length => y ∈ (origMembers m T).get i).card ≤ _
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact List.length_take_le _ _

private theorem historyLevel_zero_iff (m : MarkedIdeal n X) (T : BlowupTower X Y) (s : ℕ) (y : Y) :
    y ∈ historyLevelSuperlevel m T 0 s ↔ s ≤ level m T y := by
  cases T <;> rfl

/-- Actual finite analytic head predicates internally freeze own-level and literal run on every genuine curve component. -/
theorem exists_analytic_dimzero_stepOne_history_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (hd : 1 ≤ m.d)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) (Z : Set Y)
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1)
    (hZA : Z ⊆ (geoTransformAlong (barMarked m) T).cosupp) :
    ∃ S : Set Y, IsComplexAnalyticSubset (n := n) S ∧ DimLE (n := n) S 0 ∧ S ⊆ Z ∧
      (∀ x ∈ Z \ S, RegularAtDim (n := n) Z x 1) ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ x ∈ B \ S, ∀ y ∈ B \ S,
        level m T x = level m T y ∧
          regimeRun (stepRegime m (level m T x)) T x =
            regimeRun (stepRegime m (level m T y)) T y := by
  classical
  let I := Fin (T.length+1) × Fin (m.E.length+2) × Fin 2
  let P : I → Set Y := fun i => if i.2.2 = 0 then
    historyLevelSuperlevel m T i.1 i.2.1 else historyTopSuperlevel hn m T i.1 i.2.1
  have hP : ∀ i, IsComplexAnalyticSubset (n := n) (P i) := by
    intro i
    dsimp only [P]
    split_ifs
    · exact isComplexAnalyticSubset_historyLevelSuperlevel hn m hw T hT _ _
    · exact isComplexAnalyticSubset_historyTopSuperlevel hn m hw hd hmax T hT _ _
  obtain ⟨E, hE, hdE, hEZ, hdict⟩ := exists_analytic_dimzero_predicate_exception hZ hdZ P hP
  obtain ⟨Q, hQ, hdQ, hQZ, _, hreg⟩ := exists_analytic_dimzero_regular_curve_envelope hZ hdZ
  obtain ⟨hS, hdS⟩ := HironakaDimensionTwoStepOneAnalyticSuperlevels.analytic_dimzero_union hE hdE hQ hdQ
  refine ⟨E ∪ Q, hS, hdS, union_subset hEZ hQZ, ?_, ?_⟩
  · intro x hx
    exact hreg x ⟨hx.1, fun hxQ => hx.2 (Or.inr hxQ)⟩
  intro B hB x hx y hy
  have hxE : x ∈ B \ E := ⟨hx.1, fun hxE => hx.2 (Or.inl hxE)⟩
  have hyE : y ∈ B \ E := ⟨hy.1, fun hyE => hy.2 (Or.inl hyE)⟩
  have hcmp : ∀ i : I, x ∈ P i ↔ y ∈ P i := fun i =>
    (hdict B hB x hxE i).trans (hdict B hB y hyE i).symm
  have hlevel : ∀ (r : Fin (T.length+1)) (s : Fin (m.E.length+2)),
      x ∈ historyLevelSuperlevel m T r s ↔ y ∈ historyLevelSuperlevel m T r s := by
    intro r s
    simpa only [P, if_pos rfl] using hcmp (r, s, 0)
  have htop : ∀ (r : Fin (T.length+1)) (s : Fin (m.E.length+2)),
      x ∈ historyTopSuperlevel hn m T r s ↔ y ∈ historyTopSuperlevel hn m T r s := by
    intro r s
    have hb : (1 : Fin 2) ≠ 0 := by decide
    simpa only [P, if_neg hb] using hcmp (r, s, 1)
  have hxl := level_le_original_length m T x
  have hyl := level_le_original_length m T y
  let sx : Fin (m.E.length+2) := ⟨level m T x, by omega⟩
  let sy : Fin (m.E.length+2) := ⟨level m T y, by omega⟩
  have hxy : level m T x ≤ level m T y := by
    have hh := hlevel 0 sx
    change (x ∈ historyLevelSuperlevel m T 0 (level m T x) ↔
      y ∈ historyLevelSuperlevel m T 0 (level m T x)) at hh
    rw [historyLevel_zero_iff, historyLevel_zero_iff] at hh
    exact hh.mp le_rfl
  have hyx : level m T y ≤ level m T x := by
    have hh := hlevel 0 sy
    change (x ∈ historyLevelSuperlevel m T 0 (level m T y) ↔
      y ∈ historyLevelSuperlevel m T 0 (level m T y)) at hh
    rw [historyLevel_zero_iff, historyLevel_zero_iff] at hh
    exact hh.mpr le_rfl
  have heq := hxy.antisymm hyx
  refine ⟨heq, ?_⟩
  rw [← heq]
  apply regimeRun_eq_of_head_predicates
  intro r hr
  let rf : Fin (T.length+1) := ⟨r, by omega⟩
  let sx1 : Fin (m.E.length+2) := ⟨level m T x+1, by omega⟩
  have hxA := hZA (subset_of_mem_globalComponents hZ hB hx.1)
  have hyA := hZA (subset_of_mem_globalComponents hZ hB hy.1)
  rw [stepRegime_head_iff_history_predicates hn m hw hd hmax T hT r _ hxA,
    stepRegime_head_iff_history_predicates hn m hw hd hmax T hT r _ hyA,
    hlevel rf sx, hlevel rf sx1, htop rf sx]

open HironakaGeneralThreeNonspecialAnalyticLoci HironakaDimensionThreeStepOneCurveEnvelope
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Original true domain3/canonical inputs produce the genuine companion curve and computed history exception. -/
theorem exists_actual_companion_stepOne_history_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    ∃ Z : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) Z ∧
      DimLE (n := n) Z 1 ∧ Z ⊆ (geoTransformAlong K R).cosupp ∧
      (∀ p ∈ (geoTransformAlong K R).cosupp,
        ¬ IsSpecial K R p → p ∈ Z) ∧
      ∃ S : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) S ∧
        DimLE (n := n) S 0 ∧ S ⊆ Z ∧
        (∀ p ∈ Z \ S, RegularAtDim (n := n) Z p 1) ∧
        ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B \ S, ∀ q ∈ B \ S,
          level K R p =
            level K R q ∧
          regimeRun (stepRegime K
              (level K R p)) R p =
            regimeRun (stepRegime K
              (level K R q)) R q := by
  dsimp only
  obtain ⟨_, hK, hmax, hcanK, _⟩ :=
    actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK
  obtain ⟨Z, hZ, hdZ, hZA, hnsp⟩ :=
    exists_actual_companion_dimone_nonspecial_envelope hn m h T hcan x hx hq
  have hZbar : Z ⊆ (geoTransformAlong (barMarked (companionAt m T x)) (companionTailAt m T x)).cosupp := by
    rw [hb.2.2]
    exact hZA
  obtain ⟨S, hS, hdS, hSZ, hreg, hrun⟩ :=
    exists_analytic_dimzero_stepOne_history_exception
      (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x))
      hn (companionAt m T x)
      hK.isWellFormed hK.one_le_d hmax (companionTailAt m T x) hb.1 Z hZ hdZ hZbar
  exact ⟨Z, hZ, hdZ, hZA, hnsp, S, hS, hdS, hSZ, hreg, hrun⟩

end
end Hironaka.HironakaStepOneCurveHistoryPredicates
