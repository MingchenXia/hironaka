/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedCurveSmoothValues
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFinite
/-! Genuine source choice stagewise isomorphisms produce actual smooth
Cartesian histories before whole curve-reference GENERAL values. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSourceChoiceCartesian
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerComposition HironakaSmoothSubmersionHistoricalControlledTail
  HironakaOriginalUntestedCurveSmoothValues HironakaSmoothSubmersionCanonicalValueDimensionShift
  MarkedIdeals MarkedIdeals.MarkedIdeal InvDomainTowerAlong CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X X' D D' : CMfd.{u} n}

theorem IsTowerIso.actual_cartesian
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D}
    {Q : BlowupTower X' D'} {T : BlowupTower X D} (h : IsTowerIso Φ Q T χ) :
    IsActualTowerPullback Φ Q T χ := by
  induction h with
  | refl => exact IsActualTowerPullback.refl (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ)
  | @step Y' Y Z' Z Q T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    exact IsActualTowerPullback.step_of_actual_square ih (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism χ) hπ hπ'
      hC.symm χ₁ χ₁.contMDiff (funext hcomm)

variable {m : ℕ} {Y Y' E E' : CMfd.{u} m}

theorem IsActualTowerPullback.source_isomorphism {f : Y → X} {g : E → D}
    {Q : BlowupTower Y E} {T : BlowupTower X D} (h : IsActualTowerPullback f Q T g)
    {Φ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ Y}
    {χ : E' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E}
    {R : BlowupTower Y' E'} (hIso : IsTowerIso Φ R Q χ) :
    IsActualTowerPullback (f ∘ Φ) R T (g ∘ χ) :=
  HironakaSmoothSubmersionCartesianTowerComposition.IsActualTowerPullback.comp h (IsTowerIso.actual_cartesian hIso)

theorem original_curve_full_value_source_isomorphism (hn : 0<n) (hm : 0<m) (k : ℕ)
    {f : Y → X} {g : E → D} {Q : BlowupTower Y E} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (hT : IsGeoTestTower M T)
    {Φ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ Y}
    {χ : E' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E}
    {R : BlowupTower Y' E'} (hIso : IsTowerIso Φ R Q χ) (z : E')
    (hy : g (χ z) ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) (f ∘ Φ) M) R z=
      familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv M T (g (χ z))) :=
  modeled_curve_smooth_full_value hn hm k (IsActualTowerPullback.source_isomorphism h hIso) M M
    (fun S hS => isInvDomain_geoTransformAlong hM S hS) hT z hy

end
end Hironaka.HironakaOriginalSourceChoiceCartesian
