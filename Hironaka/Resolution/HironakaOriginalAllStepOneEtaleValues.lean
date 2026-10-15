/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPositiveStepOneSmoothValues
import Hironaka.Resolution.HironakaOriginalZeroStepOneEtaleValues
/-! One actual original smooth source history compares every unchanged
DOMAIN2 StepOne branch on ANY genuine upper TEST, in equal ambient dimension. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAllStepOneEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaOriginalPositiveStepOneSmoothValues HironakaOriginalZeroStepOneEtaleValues
open ResolutionInvariantSpec (IsInvDomain)

private theorem stepDimensionMap_cast {α β : Type} (e : β=α) (f : α → β)
    (hf : ∀ x,e ▸ f x=x) (v : ℕ ×ₗ WithTop α) :
    congrArg (fun A => ℕ ×ₗ WithTop A) e ▸ stepDimensionMap f v=v := by
  subst β
  have hfid : f=id := funext hf
  rw [hfid]
  simp [stepDimensionMap]

private theorem generalDimensionMap_cast {α β : Type} (e : β=α) (f : α → β)
    (hf : ∀ x,e ▸ f x=x) (v : ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop α)) :
    congrArg (fun A => ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop A)) e ▸
      generalDimensionMap 0 f v=v := by
  subst β
  have hfid : f=id := funext hf
  have hKey : dimensionKey 0=id := by
    funext w
    simp [dimensionKey]
  rw [hfid]
  simp [generalDimensionMap,dimensionValue,hKey]

/-- The actual zero-fibre map is identity on EVERY unchanged recursive value,
with only the genuine equality 0+k=k identifying its codomain. -/
theorem familyDimensionMap_zero (k : ℕ) (v : ValTy k) :
    (congrArg ValTy (Nat.zero_add k) ▸ familyDimensionMap 0 k v)=v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs := stepDimensionMap_cast (congrArg ValTy (Nat.zero_add k)) (familyDimensionMap 0 k) ih
    have hg := generalDimensionMap_cast
      (congrArg (fun A => ℕ ×ₗ WithTop A) (congrArg ValTy (Nat.zero_add k)))
      (stepDimensionMap (familyDimensionMap 0 k)) hs
    exact hg v

variable {n : ℕ} {X Y D : CMfd.{u} n}

private theorem stepOneInvM_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X D) (z : D) :
    congrArg (fun j => ℕ ×ₗ WithTop (ValTy j)) hab ▸
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn a) M T z=
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn b) M T z := by
  cases hab
  rfl

/-- ONE actual source history is constructed before every point/depth and all
three actual original branches; no lower TEST or canonicality is an input. -/
theorem exists_original_any_test_all_step_one_etale_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} n) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (markedPullback (m := n) f M) Q z=
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z) := by
  obtain ⟨D',Q,g,h,hQ,hZero⟩ := exists_original_any_test_zero_step_one_etale_values hf hn M hM hmax T hT
  refine ⟨D',Q,g,h,hQ,fun z hy k => ?_⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  by_cases hSpecial : IsSpecial M T (g z)
  · have hSource := (IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mpr hSpecial
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hSource,if_pos hSpecial,hLevel]
  · rcases Nat.eq_zero_or_pos (level M T (g z)) with hl | hl
    · exact hZero z hy hSpecial hl k
    · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
      have hPositive := original_positive_step_one_smooth_value_of_test hn hn k h M hM hT s z hy hSpecial hs
      rw [Nat.sub_self] at hPositive
      let e := congrArg (fun A => ℕ ×ₗ WithTop A) (congrArg ValTy (Nat.zero_add (k+1)))
      have hMap := stepDimensionMap_cast (congrArg ValTy (Nat.zero_add (k+1)))
        (familyDimensionMap 0 (k+1)) (familyDimensionMap_zero (k+1))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z))
      have hCast := congrArg (fun w => e ▸ w) hPositive
      have hFinal := hCast.trans hMap
      have hSourceCast := stepOneInvM_cast_depth hn (Nat.zero_add (k+1))
        (markedPullback (m := n) f M) Q z
      exact hSourceCast.symm.trans hFinal

end
end Hironaka.HironakaOriginalAllStepOneEtaleValues
