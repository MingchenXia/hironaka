/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedMemberOpenFullValues
import Hironaka.Resolution.HironakaSmoothSubmersionPositiveLowerHistory
import Hironaka.Resolution.HironakaOriginalContactRemainderSmoothNaturality
/-! Genuine entire controlled smooth pullback from actual coherent ideals and
actual strict-carrier geometry; no lower TEST or point-cosupport certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedControlledSmoothPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  RelativePrincipalizationSpan GermIdealPullbackCalculus RestrictedIdealExtension
  RestrictedIdealQuotient CoherentIdealColon IdealWeightPowers BlowupStrictSubmanifold
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionControlledTransform
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionPositiveLowerHistory HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionGermIdealColon
  HironakaOriginalUntestedMemberOpenFullValues HironakaOriginalContactRemainderSmoothNaturality
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneZeroContactRemainderExtension InvDomainMemberRestriction BoundaryCount
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- Actual coherent numerator and actual next strict carrier smoothness suffice
for ALL FOUR fields, with no candidate admissibility or mark restriction. -/
theorem markedPullback_geoTransform_of_smooth_strict
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    {C : Set X} {π : D → X} {ρ : D' → Y}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    (B : MarkedIdeal n X) (hI : B.ideal.IsCoherent)
    (hStrict : IsClosedSubmanifold n (geoStrictTransform π C B.N)) :
    (markedPullback (m := m) f B).geoTransform (f ⁻¹' C) ρ=
      markedPullback (m := m) (actualLift hf hπ hρ) (B.geoTransform C π) := by
  have hnum : GermIdeal.pullback (m := m) (actualLift hf hπ hρ)
      (GermIdeal.pullback (m := n) π B.ideal)=
      GermIdeal.pullback (m := m) ρ (GermIdeal.pullback (m := m) f B.ideal) := by
    rw [←coherent_pullback_comp hπ.contMDiff (actualLift_contMDiff hf hπ hρ) _ hI,
      actualLift_proj_comm hf hπ hρ,coherent_pullback_comp hf.contMDiff hρ.contMDiff _ hI]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact (geoStrictTransform_actual_preimage hf hπ hρ B.N).symm
  · exact (boundary_actual_preimage hf hπ hρ B.E).symm
  · change colonAlong m (geoStrictTransform ρ (f ⁻¹' C) (f ⁻¹' B.N))
        (GermIdeal.pullback (m := m) ρ (GermIdeal.pullback (m := m) f B.ideal))
        (idealPow (GermIdeal.pullback (m := m) ρ (vanishingIdeal (n := m) (f ⁻¹' C))) B.d)=
      GermIdeal.pullback (m := m) (actualLift hf hπ hρ)
        (colonAlong n (geoStrictTransform π C B.N) (GermIdeal.pullback (m := n) π B.ideal)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) B.d))
    rw [pullback_colonAlong_eq (HironakaSmoothSubmersionBlowupChoiceGeometry.actualLift_isSubmersion hf hπ hρ)
      (isCoherent_pullback hπ.contMDiff hI)
      (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)) B.d) hStrict,
      geoStrictTransform_actual_preimage hf hπ hρ B.N,hnum,
      pullback_idealPow (actualLift_contMDiff hf hπ hρ)
        (isCoherent_pullback hπ.contMDiff (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)),
      actualLift_whole_ideal hf hπ hρ]
  · rfl

/-- The generic hypothesis is real reference geometry, supplied internally by
original member data below. Neither reference history is claimed to be a TEST. -/
theorem IsActualTowerPullback.modeled_controlled_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong K R).IsWellFormed) (hT : IsGeoTestTower M T) :
    geoTransformAlong (markedPullback (m := m) f K) Q=markedPullback (m := m) g (geoTransformAlong K T) ∧
      (geoTransformAlong (markedPullback (m := m) f K) Q).cosupp=g ⁻¹' (geoTransformAlong K T).cosupp := by
  have hWhole : geoTransformAlong (markedPullback (m := m) f K) Q=markedPullback (m := m) g (geoTransformAlong K T) := by
    induction h with
    | refl => rfl
    | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
      obtain ⟨hTT,_hC⟩ := hT
      have hPrev := hModel T hTT
      have hNext := hModel (.step T C π hπ) ⟨hTT,_hC⟩
      change (geoTransformAlong (markedPullback (m := m) f K) Q).geoTransform (g ⁻¹' C) ρ=
        markedPullback (m := m) (actualLift hg hπ hρ) ((geoTransformAlong K T).geoTransform C π)
      rw [ih hTT]
      exact markedPullback_geoTransform_of_smooth_strict hg hπ hρ (geoTransformAlong K T)
        hPrev.isCoherent hNext.isClosedSubmanifold_N
  refine ⟨hWhole,?_⟩
  rw [hWhole]
  exact cosupport_preimage_eq h.isSubmersion (hModel T hT).isCoherent (geoTransformAlong K T).N (geoTransformAlong K T).d

/-- ONLY original DOMAIN2/nonempty actual member positions and ANY upper TEST
internally supply every genuine reference geometry used in the entire recursion. -/
theorem original_member_untested_controlled_dictionary (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (S : Finset (Fin M.E.length)) (hS : S.Nonempty) (hT : IsGeoTestTower M T) :
    geoTransformAlong (markedPullback (m := m) f (memberRemainderMarked M S)) Q=
      markedPullback (m := m) g (geoTransformAlong (memberRemainderMarked M S) T) ∧
    (geoTransformAlong (markedPullback (m := m) f (memberRemainderMarked M S)) Q).cosupp=
      g ⁻¹' (geoTransformAlong (memberRemainderMarked M S) T).cosupp := by
  exact IsActualTowerPullback.modeled_controlled_dictionary h M (memberRemainderMarked M S)
    (fun R hR => (isInvDomain_geoTransformAlong_memberRemainder hn M hM.isWellFormed hM.one_le_d hM.dimLE S hS R hR).isWellFormed) hT

/-- True whole coefficient/member and remaining-component smooth naturality
identify the INDEPENDENT source remainder, retaining its literal ordered family. -/
theorem markedPullback_memberRemainder_membersThrough (hn : 0<n) (hm : 0<m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : 1≤M.d)
    (E₀ : List (Set X)) (hE₀ : ∀ F ∈ E₀,F ∈ M.E) (z : Y) :
    markedPullback (m := m) f (memberRemainderMarked M (membersThrough M.E E₀ (f z)))=
      memberRemainderMarked (X := Y) (markedPullback (m := m) f M)
        (membersThrough (markedPullback (m := m) f M).E (E₀.map (f ⁻¹' ·)) z) := by
  let S := membersThrough M.E E₀ (f z)
  have hR := isWellFormed_memberRestrict hn hM S
  rw [memberRemainderMarked_eq_contactRemainder_zero hn M hM hd S,
    contactRemainderMarked_markedPullback hf (memberRestrict M S)
      hR.isClosedSubmanifold_N hR.isCoherent (one_le_memberRestrict_d M S) 0]
  rw [markedPullback_memberRestrict_membersThrough hf M hM E₀ hE₀ z]
  exact (memberRemainderMarked_eq_contactRemainder_zero hm (markedPullback (m := m) f M)
    (isWellFormed_markedPullback_submersion hf M hM) hd _).symm

/-- Independent actual SOURCE member records and EVERY literal prefix are
constructed from ONLY original input before whole controlled/cosupport equality. -/
theorem original_through_member_untested_all_heads_dictionary (hn : 0<n) (hm : 0<m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (E₀ : List (Set X)) (hE₀ : ∀ F ∈ E₀,F ∈ M.E) (z₀ : Y)
    (hPos : 1≤boundaryCount E₀ (f z₀)) (hT : IsGeoTestTower M T) :
    let K := memberRemainderMarked M (membersThrough M.E E₀ (f z₀))
    let K' := memberRemainderMarked (X := Y) (markedPullback (m := m) f M)
      (membersThrough (markedPullback (m := m) f M).E (E₀.map (f ⁻¹' ·)) z₀)
    (geoTransformAlong K' Q=markedPullback (m := m) g (geoTransformAlong K T) ∧
      (geoTransformAlong K' Q).cosupp=g ⁻¹' (geoTransformAlong K T).cosupp) ∧
    ∀ j : ℕ,∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      geoTransformAlong K' (head Q j)=markedPullback (m := m) a (geoTransformAlong K (head T j)) ∧
      (geoTransformAlong K' (head Q j)).cosupp=a ⁻¹' (geoTransformAlong K (head T j)).cosupp := by
  let S := membersThrough M.E E₀ (f z₀)
  have hS : S.Nonempty := membersThrough_nonempty hE₀ hPos
  have hInit := markedPullback_memberRemainder_membersThrough hn hm hf M hM.isWellFormed hM.one_le_d E₀ hE₀ z₀
  have hWhole := original_member_untested_controlled_dictionary hn h M hM S hS hT
  dsimp only
  rw [hInit] at hWhole
  refine ⟨hWhole,fun j => ?_⟩
  obtain ⟨a,ha⟩ := h.head j
  have hTJ := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hHead := original_member_untested_controlled_dictionary hn ha M hM S hS hTJ
  rw [hInit] at hHead
  exact ⟨a,ha,hHead⟩

end
end Hironaka.HironakaOriginalUntestedControlledSmoothPullback
