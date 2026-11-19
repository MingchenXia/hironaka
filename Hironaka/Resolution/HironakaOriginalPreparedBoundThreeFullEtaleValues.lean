/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentCompanionEtaleValues
import Hironaka.Resolution.HironakaOriginalPreparedCompanionSmoothDiagram
/-! Unchanged ORIGINAL FULL source-bound-three values after one genuine
possibly noncanonical preparation, then literal open and nested locality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedBoundThreeFullEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  StepOneRegime HomogenizedIdealAlong HironakaOriginalPreparedCurrentCompanionEtaleValues
  HironakaOriginalPreparedCompanionSmoothDiagram HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalAllStepOneEtaleValues HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionActualFamilyMonomialLeaf
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X D Z A B : CMfd.{u} n}

private theorem domain_three_at_depth (M : MarkedIdeal n X) (hM : IsInvDomain 3 M) (d : ℕ) :
    IsInvDomain (d+3) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

private theorem family_value_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X D) (z : D) :
    (congrArg ValTy hab ▸ (invFamily hn a).inv M T z)=
      (invFamily hn b).inv M T z := by
  cases hab
  rfl

/-- Actual CURRENT companion geometry and values precede literal GENERAL;
no next canonicality or old/current companion equality is assumed. -/
theorem prepared_bound_three_full_etale_values
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 3).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 3).inv M T x≤(invFamily hn 3).inv M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g)
    (z : B) (hz : g z∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+3)).inv (markedPullback (m := n) f M) Q z=
      (invFamily hn (d+3)).inv M (.step T C π hπ) (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hT := (invFamily hn 3).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M P := ⟨hT,hC⟩
  by_cases hZero : nmOrd (geoTransformAlong M P) (g z)=0
  · have hv := (IsActualTowerPullback.actual_family_monomial_leaf hn hn h M
      (domain_three_at_depth M hM d) hP z hZero).2
    rw [Nat.sub_self] at hv
    have hCast := congrArg
      (fun v : ValTy (0+(d+3)) => congrArg ValTy (Nat.zero_add (d+3)) ▸ v) hv
    have hLeft := family_value_cast_depth hn (Nat.zero_add (d+3))
      (markedPullback (m := n) f M) Q z
    exact hLeft.symm.trans (hCast.trans
      (familyDimensionMap_zero (d+3) ((invFamily hn (d+3)).inv M P (g z))))
  have hPos : 0<nmOrd (geoTransformAlong M P) (g z) := Nat.pos_of_ne_zero hZero
  obtain ⟨hOrd,hRun,hp,hp',p,q,hRecord,hCart,_hCoord,hPoint,hDom,hMax,hTest,
    _hCurrent,hTargetPoint,_hSourceDom,_hSourceTest,_hSourceCurrent,_hSourcePoint,_hWhole,_hCos,_hHeads⟩ :=
    prepared_current_companion_smooth_diagram (k := 2) hn M hM T hc C hC π hπ
      (fun x hx _ => hCuts x hx) h z hz hPos
  let o := nmOrd (geoTransformAlong M P) (g z)
  have ho : 0<o := hPos
  let r := regimeRun (OrdRegime M o) P (g z)
  let U := ordMask (geoTransformAlong M (head P r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := n) f M) (head Q r)) o
  let J := compAt M o (head P r)
  let J' := compAt (markedPullback (m := n) f M) o (head Q r)
  let R := restrict U (tail P r)
  let R' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  change markedPullback (m := n) p J=J' at hRecord
  change IsActualTowerPullback p R' R q at hCart
  have hTarget : q z'∈(geoTransformAlong J R).cosupp := by
    rw [hPoint]
    exact hTargetPoint
  have hValues := current_companion_step_one_etale_values_after_full_cut
    hn M hM T hc C hC π hπ hCuts (g z) hz hPos
  have hv := hValues.2.2.2 hCart z' hTarget d
  rw [hRecord,hPoint] at hv
  change genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hn (d+2)) K (Y := B) S w) (markedPullback (m := n) f M) Q z=
    genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hn (d+2)) K (Y := B) S w) M P (g z)
  unfold genInv genSecond
  rw [hOrd,show nmOrd (geoTransformAlong M P) (g z)=o from rfl,
    if_neg (ne_of_gt ho),hRun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho)]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy (d+2)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy (d+2))))))) hv

/-- The literal open Cartesian history is constructed before prepared FULL
comparison, preserving the exact point and EVERY empty restriction. -/
theorem prepared_bound_three_full_value_restrict_open
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 3).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 3).inv M T x≤(invFamily hn 3).inv M T c)
    (U : Opens X) (z : openPreimage (.step T C π hπ) U)
    (hz : z.val∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+3)).inv (markedPullback (m := n) (Subtype.val : U → X) M)
      (restrict U (.step T C π hπ)) z=
        (invFamily hn (d+3)).inv M (.step T C π hπ) z.val := by
  exact prepared_bound_three_full_etale_values hn M hM T hc C hC π hπ hCuts
    (open_inclusion_actual_tower U (.step T C π hπ)) z hz d

/-- Both nested restrictions compare through the SAME actual original value
at the SAME underlying current point, without next canonicality. -/
theorem prepared_bound_three_full_value_nested_open
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 3).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 3).inv M T x≤(invFamily hn 3).inv M T c)
    (U V : Opens X) (hVU : V≤U) (z : openPreimage (.step T C π hπ) V)
    (hz : z.val∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+3)).inv (markedPullback (m := n) (Subtype.val : V → X) M)
      (restrict V (.step T C π hπ)) z=
    (invFamily hn (d+3)).inv (markedPullback (m := n) (Subtype.val : U → X) M)
      (restrict U (.step T C π hπ)) ⟨z.val,hVU z.property⟩ := by
  exact (prepared_bound_three_full_value_restrict_open hn M hM T hc C hC π hπ hCuts V z hz d).trans
    (prepared_bound_three_full_value_restrict_open hn M hM T hc C hC π hπ hCuts U
      ⟨z.val,hVU z.property⟩ hz d).symm

end
end Hironaka.HironakaOriginalPreparedBoundThreeFullEtaleValues
