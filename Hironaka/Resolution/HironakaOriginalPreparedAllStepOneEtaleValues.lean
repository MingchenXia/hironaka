/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedZeroOwnLargeEtaleValues
import Hironaka.Resolution.HironakaOriginalPreparedPositiveStepOneValues
import Hironaka.Resolution.HironakaOriginalAllStepOneEtaleValues
/-! SAME given prepared equal-dimensional history compares all unchanged
original StepOne branches at the genuine source-bound-three base. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedAllStepOneEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower
  StepOneValue StepOneLowerDomain StepOneValueMasked StepOneRegime
  HironakaOriginalPreparedZeroOwnLargeEtaleValues HironakaOriginalPreparedPositiveStepOneValues
  HironakaOriginalAllStepOneEtaleValues HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z A B : CMfd.{u} n}

private theorem stepDimensionMap_cast {α β : Type} (e : β=α) (f : α → β)
    (hf : ∀ x,e ▸ f x=x) (v : ℕ ×ₗ WithTop α) :
    congrArg (fun A => ℕ ×ₗ WithTop A) e ▸ stepDimensionMap f v=v := by
  subst β
  have hfid : f=id := funext hf
  rw [hfid]
  simp [stepDimensionMap]

private theorem stepOneInvM_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg (fun j => ℕ ×ₗ WithTop (ValTy j)) hab ▸
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn a) M T z=
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn b) M T z := by
  cases hab
  rfl

/-- Genuine independent OWN-large values and actual mask memberships precede
literal evaluation of the unchanged original zero StepOne branch. -/
theorem prepared_zero_step_one_etale_values
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) (z : B)
    (hy : g z∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) (g z))
    (hl : level M (.step T C π hπ) (g z)=0) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) (markedPullback (m := n) f M) Q z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M (.step T C π hπ) (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  let K := markedPullback (m := n) f M
  let r := regimeRun (stepRegime M 0) P (g z)
  let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
  let V := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hpOwn,hValues⟩ := (original_prepared_zero_own_large_etale_values
    hn M hM hmax T hcan C hC π hπ hCuts h).2 z hy hns hl
  let yU : openPreimage (tail P r) U := ⟨g z,hp⟩
  let zV : openPreimage (tail Q r) V := ⟨z,hpOwn⟩
  have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 2) M hM hmax hn T hcan).2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  have hRun : regimeRun (stepRegime K (level K Q z)) Q z=r := by
    rw [hLevel,hl]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed hBar 0 z
  have hnsSource : ¬IsSpecial K Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mp hs)
  have hSource : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) K Q z=
      toLex (0,((invFamily hn (d+2)).inv JOwn (restrict V (tail Q r)) zV : WithTop (ValTy (d+2)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hnsSource,hRun,hLevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hpOwn]
  have hTarget : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M P (g z)=
      toLex (0,((invFamily hn (d+2)).inv J (restrict U (tail P r)) yU : WithTop (ValTy (d+2)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hSource,hTarget]
  exact congrArg (fun v : ValTy (d+2) => toLex (0,(v : WithTop (ValTy (d+2))))) (hValues d)

/-- The SAME GIVEN actual source history precedes all points, depths and
special/zero/positive branches. No next canonicality is assumed. -/
theorem prepared_all_step_one_etale_values
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      ∀ z : B,g z∈(geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) (markedPullback (m := n) f M) Q z=
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M (.step T C π hπ) (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 2) M hM hmax hn T hcan).2.1,hC⟩
  have hQ := (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hP).1
  refine ⟨hQ,?_⟩
  intro z hy d
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  by_cases hsp : IsSpecial M P (g z)
  · have hSource := (IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mpr hsp
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hSource,if_pos hsp,hLevel]
  · by_cases hl : level M P (g z)=0
    · exact prepared_zero_step_one_etale_values hn M hM hmax T hcan C hC π hπ hCuts h z hy hsp hl d
    · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hl
      have hPositive := prepared_positive_step_one_smooth_values hn hn M hM hmax T hcan C hC π hπ hCuts h s z hy hsp hs d
      rw [Nat.sub_self] at hPositive
      let e := congrArg (fun A => ℕ ×ₗ WithTop A) (congrArg ValTy (Nat.zero_add (d+2)))
      have hMap := stepDimensionMap_cast (congrArg ValTy (Nat.zero_add (d+2)))
        (familyDimensionMap 0 (d+2)) (familyDimensionMap_zero (d+2))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M P (g z))
      have hCast := congrArg (fun w => e ▸ w) hPositive
      have hFinal := hCast.trans hMap
      have hSourceCast := stepOneInvM_cast_depth hn (Nat.zero_add (d+2))
        (markedPullback (m := n) f M) Q z
      exact hSourceCast.symm.trans hFinal

end
end Hironaka.HironakaOriginalPreparedAllStepOneEtaleValues
