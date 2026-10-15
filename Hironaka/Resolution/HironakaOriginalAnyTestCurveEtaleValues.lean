/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnyTestCurveFullValue
import Hironaka.Resolution.HironakaSmoothSubmersionRelativePartsCompanion
/-! Actual equal-ambient-dimension smooth naturality of unchanged full
curve invariants on ANY original TEST, without canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAnyTestCurveEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  RelativePrincipalizationSpan NonmonomialOrderLocal MonomialCaseAlong CanonicalCentres
  HironakaOriginalAnyTestCurveFullValue HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativePartsCompanion
  HironakaSmoothSubmersionRelativeMonomial
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y D D' : CMfd.{u} n}

/-- Real source domain/TEST/BOTHcosupport precede unchanged full values;
only the true ANYTEST curve formula and whole smooth Nm/gamma dictionaries. -/
theorem actual_original_curve_full_values_etale {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    {T : BlowupTower X D} {Q : BlowupTower Y D'} {g : D' → D}
    (h : IsActualTowerPullback f Q T g) (hT : IsGeoTestTower M T) :
    IsInvDomain 1 (markedPullback (m := n) f M) ∧
      IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      (geoTransformAlong (markedPullback (m := n) f M) Q).cosupp=
        g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ p : D',g p ∈ (geoTransformAlong M T).cosupp → ∀ k : ℕ,
        (invFamily hn (k+1)).inv (markedPullback (m := n) f M) Q p=
          (invFamily hn (k+1)).inv M T (g p) := by
  have hSource : IsInvDomain 1 (markedPullback (m := n) f M) := by
    simpa only [Nat.sub_self,Nat.add_zero] using isInvDomain_markedPullback_submersion hf M hM
  obtain ⟨hQ,hCurrent⟩ := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT
  have hCos := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hT
  have hStage := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  refine ⟨hSource,hQ,hCos,fun p hp k => ?_⟩
  have hpQ : p ∈ (geoTransformAlong (markedPullback (m := n) f M) Q).cosupp := by
    rw [hCos]
    exact hp
  have hOrd : nmOrd (geoTransformAlong (markedPullback (m := n) f M) Q) p=
      nmOrd (geoTransformAlong M T) (g p) := by
    rw [hCurrent]
    exact nmOrd_markedPullback h.isSubmersion hn _ hStage.isWellFormed hStage.isNonzeroAlongAt p
  have hGamma : gammaAlong n (geoTransformAlong (markedPullback (m := n) f M) Q).N
      (geoTransformAlong (markedPullback (m := n) f M) Q).ideal
      (geoTransformAlong (markedPullback (m := n) f M) Q).E
      (geoTransformAlong (markedPullback (m := n) f M) Q).d p=
      gammaAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E (geoTransformAlong M T).d (g p) := by
    rw [hCurrent]
    exact gammaAlong_same_dimension_preimage_eq h.isSubmersion hStage.isWellFormed.isCoherent rfl
      (geoTransformAlong M T).N (geoTransformAlong M T).E (geoTransformAlong M T).d p
  rw [original_curve_any_test_full_value_formula hn k _ hSource Q hQ p hpQ,
    original_curve_any_test_full_value_formula hn k M hM T hT (g p) hp,hOrd,hGamma]

/-- ONLY original data construct the SAME actual Cartesian source history
before all positive-depth unchanged full original values on ANY target TEST. -/
theorem exists_original_curve_any_test_etale_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} n) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      IsInvDomain 1 (markedPullback (m := n) f M) ∧ IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      geoTransformAlong (markedPullback (m := n) f M) Q=markedPullback (m := n) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := n) f M) Q).cosupp=g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ p : D',g p ∈ (geoTransformAlong M T).cosupp → ∀ k : ℕ,
        (invFamily hn (k+1)).inv (markedPullback (m := n) f M) Q p=(invFamily hn (k+1)).inv M T (g p) := by
  obtain ⟨D',Q,g,h,hg,_hLen,_hSquare,_hQ,hCurrent,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  obtain ⟨hSource,hQ,hCos,hValue⟩ := actual_original_curve_full_values_etale hf hn M hM h hT
  exact ⟨D',Q,g,h,hg,hSource,hQ,hCurrent,hCos,hValue⟩

end
end Hironaka.HironakaOriginalAnyTestCurveEtaleValues
