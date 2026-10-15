/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnyTestCurveFullValue
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
/-! Exact ALL-depth original curve FULL values on ANY original TEST under
actual open restriction and true tower isomorphisms, without canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAnyTestCurveValueNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport RelativePrincipalizationSpan
  NonmonomialOrderLocal MonomialInvariantFunctorialAlong MonomialCaseAlong CanonicalCentres
  HironakaOriginalAnyTestCurveFullValue
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y X' Y' : CMfd.{u} n}

/-- Internally actual restricted domain/TEST/cosupport precede full values;
only genuine ANYTEST order/gamma geometry is used after the actual formula. -/
theorem original_curve_any_test_full_value_restrict (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (U : Opens X)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (p : openPreimage T U)
    (hp : p.val ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) p=
      (invFamily hn (k+1)).inv M T p.val := by
  have hMU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hTU := isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hEq := geoTransformAlong_restrict U hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  have hCos : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp := by
    rw [hEq,cosupp_pullback_val _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent hg)]
    exact hp
  have hOrd : nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)) p=
      nmOrd (geoTransformAlong M T) p.val := by
    rw [hEq]
    exact nmOrd_pullback_val hn hCurrent.isWellFormed hCurrent.isNonzeroAlongAt (openPreimage T U) p
  have hGamma : gammaAlong n (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).N
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).ideal
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).d p=
      gammaAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal (geoTransformAlong M T).E
        (geoTransformAlong M T).d p.val := by
    rw [hEq]
    exact gammaAlong_pullback_val (geoTransformAlong M T)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent hg)
      (openPreimage T U) p _
  rw [original_curve_any_test_full_value_formula (X := CMfd.of (n := n) U)
    (Y := CMfd.of (n := n) (openPreimage T U)) hn k _ hMU _ hTU p hCos,
    original_curve_any_test_full_value_formula hn k M hM T hT p.val hp,hOrd,hGamma]

/-- Actual isomorphic source DOMAIN1/TEST/cosupport are constructed before
ANY original full value comparison; no CAN interface is invoked. -/
theorem original_curve_any_test_full_value_isTowerIso (hn : 0<n) (k : ℕ)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    {Q : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hi : IsTowerIso Φ Q T χ) (hT : IsGeoTestTower M T) (p : Y')
    (hp : χ p ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback Φ M) Q p=(invFamily hn (k+1)).inv M T (χ p) := by
  have hMQ := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hQ := (IsTowerIso.isGeoTestTower_iff Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hi).mpr hT
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hEq := IsTowerIso.geoTransformAlong_eq Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hi hT
  have hCos : p ∈ (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).cosupp := by
    rw [IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hi hT]
    exact hp
  have hOrd := nmOrd_geoTransformAlong_isTowerIso hn Φ hM hi hT p
  have hGamma : gammaAlong n (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).N
      (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).ideal (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).E
      (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).d p=
      gammaAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal (geoTransformAlong M T).E
        (geoTransformAlong M T).d (χ p) := by
    rw [hEq]
    exact gammaAlong_pullback_diffeomorph χ (geoTransformAlong M T)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent hg) p _
  rw [original_curve_any_test_full_value_formula hn k _ hMQ _ hQ p hCos,
    original_curve_any_test_full_value_formula hn k M hM T hT (χ p) hp,hOrd,hGamma]

/-- ONLY original inputs internally use the actual transported tower and true
back biholomorphism before exact ALL-depth full values on every original TEST. -/
theorem original_curve_any_test_full_value_transport (hn : 0<n) (k : ℕ)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (p : (transport Φ T).target) (hp : (transport Φ T).back p ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback Φ M) (transport Φ T).tower p=
      (invFamily hn (k+1)).inv M T ((transport Φ T).back p) := by
  exact original_curve_any_test_full_value_isTowerIso hn k Φ M hM (transport_isTowerIso Φ T) hT p hp

end
end Hironaka.HironakaOriginalAnyTestCurveValueNaturality
