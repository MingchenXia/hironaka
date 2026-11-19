/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedGeneralSmoothValues
import Hironaka.Resolution.HironakaOriginalAllStepOneEtaleValues
/-! Literal original FULL values on the SAME genuine open restrictions after
one actual preparation in carrier-bound two. No next canonicality is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedBoundTwoOpenLocality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres GeneralValue BlowupRestrictOpen
  HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaOriginalPreparedGeneralSmoothValues HironakaOriginalAllStepOneEtaleValues
  HironakaOriginalUntestedCurveSmoothValues
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X D Z : CMfd.{u} n}

private theorem family_value_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X D) (z : D) :
    (congrArg ValTy hab ▸ (invFamily hn a).inv M T z)=
      (invFamily hn b).inv M T z := by
  cases hab
  rfl

/-- The actual open Cartesian history is constructed before the prepared
comparison; only true equal-depth casts and the genuine zero-fibre map remain. -/
theorem prepared_bound_two_full_value_restrict_open
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 2).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 2).inv M T y≤(invFamily hn 2).inv M T c)
    (U : Opens X) (z : openPreimage (.step T C π hπ) U)
    (hz : z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+2)).inv (markedPullback (m := n) (Subtype.val : U → X) M)
      (restrict U (.step T C π hπ)) z=
        (invFamily hn (d+2)).inv M (.step T C π hπ) z.val := by
  have hv := prepared_original_general_smooth_values hn hn M hM T hc C hC π hπ
    (fun y hy _hp => hCuts y hy) (open_inclusion_actual_tower U (.step T C π hπ)) z hz d
  rw [Nat.sub_self] at hv
  have hCast := congrArg
    (fun v : ValTy (0+(d+2)) => congrArg ValTy (Nat.zero_add (d+2)) ▸ v) hv
  have hLeft := family_value_cast_depth hn (Nat.zero_add (d+2))
    (markedPullback (m := n) (Subtype.val : U → X) M) (restrict U (.step T C π hπ)) z
  exact hLeft.symm.trans (hCast.trans
    (familyDimensionMap_zero (d+2) ((invFamily hn (d+2)).inv M (.step T C π hπ) z.val)))

/-- Both actual restricted values are compared through the SAME post-step
original value at the SAME underlying point, without next canonicality. -/
theorem prepared_bound_two_full_value_nested_open
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 2).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 2).inv M T y≤(invFamily hn 2).inv M T c)
    (U V : Opens X) (hVU : V≤U) (z : openPreimage (.step T C π hπ) V)
    (hz : z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+2)).inv (markedPullback (m := n) (Subtype.val : V → X) M)
      (restrict V (.step T C π hπ)) z=
    (invFamily hn (d+2)).inv (markedPullback (m := n) (Subtype.val : U → X) M)
      (restrict U (.step T C π hπ)) ⟨z.val,hVU z.property⟩ := by
  exact (prepared_bound_two_full_value_restrict_open hn M hM T hc C hC π hπ hCuts V z hz d).trans
    (prepared_bound_two_full_value_restrict_open hn M hM T hc C hC π hπ hCuts U
      ⟨z.val,hVU z.property⟩ hz d).symm

end
end Hironaka.HironakaOriginalPreparedBoundTwoOpenLocality
