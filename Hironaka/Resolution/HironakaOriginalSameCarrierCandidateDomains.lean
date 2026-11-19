/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroOwnSmallSmoothValues
/-! Original arbitrary-bound actual candidate geometry/whole records,
without treating a raw candidate history as a TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSameCarrierCandidateDomains
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalUntestedMemberOpenFullValues HironakaOriginalUntestedControlledSmoothPullback
  HironakaOriginalUntestedSpecialSmoothPullback HironakaOriginalUntestedCurveSmoothValues
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativePartsCompanion HironakaSmoothSubmersionRelativeControlledTower
  HironakaCoherentTransformExtension HomogenizedIdealAlong HomogenizedIdealAlongTower
  InvDomainCompanion InvDomainTowerAlong CompanionReductionAlong StepOneRegime StepOneValue
  HironakaStepOneMemberTailExtension HironakaSmoothSubmersionRelativeGeometry
  HironakaOriginalCurvePositiveEmptyWindow HironakaSmoothSubmersionPositiveMemberHistory CompanionRebase
open ResolutionInvariantSpec (IsInvDomain)
variable {n m b : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

theorem same_carrier_candidate_domains (m K B : MarkedIdeal n X) (hB : IsInvDomain b B)
    (hN : B.N=K.N) (hE : B.E=K.E)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain b (geoTransformAlong K R)) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain b (geoTransformAlong B R)
  | _,.refl,_ => hB
  | _,.step R C π hπ,hR => by
    have hPrev := same_carrier_candidate_domains m K B hB hN hE hModel R hR.1
    have hNext := hModel (.step R C π hπ) hR
    have hN' := geoTransformAlong_N_eq_of_N_eq hN (.step R C π hπ)
    have hE' := geoTransformAlong_E_eq_of_E_eq hE (.step R C π hπ)
    have hSM : IsClosedSubmanifold n ((geoTransformAlong B R).geoTransform C π).N := by
      change IsClosedSubmanifold n (geoTransformAlong B (.step R C π hπ)).N
      rw [hN'];exact hNext.isWellFormed.isClosedSubmanifold_N
    refine ⟨⟨hSM,isCoherent_geoTransform_ideal_of_smooth_strict _ hPrev.isWellFormed.isCoherent hπ hSM,?_,?_⟩,?_,?_,?_⟩
    · rw [hE'];exact hNext.isWellFormed.isSNCDivisor
    · rw [hN',hE'];exact hNext.isWellFormed.isTransverse
    · rw [hN'];exact hNext.dimLE
    · rw [d_geoTransformAlong];exact hB.one_le_d
    · exact isNonzeroAlongAt_geoTransform_of_smooth_strict _ hPrev.isWellFormed.isClosedSubmanifold_N
        hPrev.isWellFormed.isCoherent hπ hSM hPrev.isNonzeroAlongAt

/-- Real original TEST geometry supplies every arbitrary-bound candidate bar
field, without treating the companion history as an admissible TEST. -/
theorem original_companion_bar_domains (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) (q : ℕ) (hq : 1≤q) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong (barMarked (companionOf n M q)) R) := by
  have hC : IsInvDomain b (companionOf n M q) := isInvDomain_companionAlong hn hM hq
  have hB := isInvDomain_barMarked (companionOf n M q) hC
  apply same_carrier_candidate_domains M M (barMarked (companionOf n M q)) hB
  · simp only [barMarked_N,companionOf,companionAlong_N]
  · simp only [barMarked_E,companionOf,companionAlong_E]
  · exact fun R hR => isInvDomain_geoTransformAlong hM R hR

private theorem actual_base_submersion {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D} (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem original_companion_bar_smooth_current (hn : 0<n)
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (q : ℕ) (hq : 1≤q) (hT : IsGeoTestTower M T) :
    let B := barMarked (companionOf n M q)
    let B' := barMarked (companionOf m (markedPullback (m := m) f M) q)
    geoTransformAlong B' Q=markedPullback (m := m) g (geoTransformAlong B T) ∧
      (geoTransformAlong B' Q).cosupp=g ⁻¹' (geoTransformAlong B T).cosupp ∧
      IsInvDomain b (geoTransformAlong B T) ∧ IsInvDomain (b+(m-n)) (geoTransformAlong B' Q) := by
  let C := companionOf n M q
  let B := barMarked C
  let B' := barMarked (companionOf m (markedPullback (m := m) f M) q)
  have hC : IsInvDomain b C := isInvDomain_companionAlong hn hM hq
  have hf := actual_base_submersion h
  have hInit : markedPullback (m := m) f B=B' := by
    rw [pullback_barMarked hf C hC.isWellFormed,
      markedPullback_companionOf hf hn M hM.isWellFormed hM.isNonzeroAlongAt q]
  have hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong B R) := fun R hR =>
    original_companion_bar_domains hn M hM q hq R hR
  have hWhole := IsActualTowerPullback.modeled_controlled_dictionary h M B
    (fun R hR => (hModel R hR).isWellFormed) hT
  rw [hInit] at hWhole
  have hD := hModel T hT
  have hSource := isInvDomain_markedPullback_submersion h.isSubmersion (geoTransformAlong B T) hD
  rw [←hWhole.1] at hSource
  exact ⟨hWhole.1,hWhole.2,hD,hSource⟩

theorem original_companion_special_level_smooth (hn : 0<n)
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (q : ℕ) (hq : 1≤q) (hT : IsGeoTestTower M T) (z : D') :
    (IsSpecial (companionOf m (markedPullback (m := m) f M) q) Q z ↔
      IsSpecial (companionOf n M q) T (g z)) ∧
    level (companionOf m (markedPullback (m := m) f M) q) Q z=level (companionOf n M q) T (g z) := by
  let C := companionOf n M q
  have hC : IsInvDomain b C := isInvDomain_companionAlong hn hM hq
  have hf := actual_base_submersion h
  have hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked C) R).IsWellFormed :=
    fun R hR => (original_companion_bar_domains hn M hM q hq R hR).isWellFormed
  have hSpecial := IsActualTowerPullback.modeled_isSpecial_dictionary h M C hC.isWellFormed hModel hT z
  have hLevel := IsActualTowerPullback.modeled_level_dictionary h M C hC.isWellFormed hModel hT z
  rw [markedPullback_companionOf hf hn M hM.isWellFormed hM.isNonzeroAlongAt q] at hSpecial hLevel
  exact ⟨hSpecial,hLevel⟩

end
end Hironaka.HironakaOriginalSameCarrierCandidateDomains
