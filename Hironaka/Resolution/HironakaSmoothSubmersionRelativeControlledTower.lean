/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionControlledTransform
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionRelativeControlledTower
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothSubmersionControlledTransform HironakaSmoothSubmersionGermIdealColon
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionCartesianTower GermIdealPullbackCalculus
  RestrictedIdealExtension RestrictedIdealQuotient CoherentIdealColon IdealWeightPowers
  BlowupTowers BlowupStrictSubmanifold HironakaSmoothSubmersionOrderedChoiceImageTrace
  MarkedIdeals MarkedIdeals.MarkedIdeal
noncomputable section
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {C N : Set X} {π : D → X} {ρ : D' → Y}

theorem pullback_restrictOn_eq
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := m) f (restrictOn n N I) =
      restrictOn m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) := by
  rw [restrictOn_eq_sum_vanishingIdeal hI,
    pullback_sumIdeal_dimensions hf.contMDiff hI
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hN),
    pullback_vanishingIdeal_submersion hf hN,
    restrictOn_eq_sum_vanishingIdeal (isCoherent_pullback hf.contMDiff hI)]

theorem pullback_colonAlong_eq
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I L : GermIdeal n X} (hI : I.IsCoherent) (hL : L.IsCoherent)
    (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := m) f (colonAlong n N I L) =
      colonAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I)
        (GermIdeal.pullback (m := m) f L) := by
  unfold colonAlong
  rw [HironakaSmoothSubmersionGermIdealColon.pullback_colon_eq hf
    (restrictOn n N I) L (isCoherent_restrictOn_of_isClosedSubmanifold hI hN) hL,
    pullback_restrictOn_eq hf hI hN]

theorem markedPullback_geoTransform_actual_relative
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hC : M.IsAdmissibleCentre C) :
    (markedPullback (m := m) f M).geoTransform (f ⁻¹' C) ρ =
      markedPullback (m := m) (actualLift hf hπ hρ) (M.geoTransform C π) := by
  have hstrict := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold
    hπ hM.isClosedSubmanifold_N hC.subset_N
  have hnum : GermIdeal.pullback (m := m) (actualLift hf hπ hρ)
      (GermIdeal.pullback (m := n) π M.ideal) =
      GermIdeal.pullback (m := m) ρ (GermIdeal.pullback (m := m) f M.ideal) := by
    rw [← coherent_pullback_comp hπ.contMDiff (actualLift_contMDiff hf hπ hρ) _ hM.isCoherent,
      actualLift_proj_comm hf hπ hρ,
      coherent_pullback_comp hf.contMDiff hρ.contMDiff _ hM.isCoherent]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact (geoStrictTransform_actual_preimage hf hπ hρ M.N).symm
  · exact (boundary_actual_preimage hf hπ hρ M.E).symm
  · change colonAlong m (geoStrictTransform ρ (f ⁻¹' C) (f ⁻¹' M.N))
        (GermIdeal.pullback (m := m) ρ (GermIdeal.pullback (m := m) f M.ideal))
        (idealPow (GermIdeal.pullback (m := m) ρ (vanishingIdeal (n := m) (f ⁻¹' C))) M.d) =
      GermIdeal.pullback (m := m) (actualLift hf hπ hρ)
        (colonAlong n (geoStrictTransform π C M.N) (GermIdeal.pullback (m := n) π M.ideal)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d))
    rw [pullback_colonAlong_eq (HironakaSmoothSubmersionBlowupChoiceGeometry.actualLift_isSubmersion hf hπ hρ)
      (isCoherent_pullback hπ.contMDiff hM.isCoherent)
      (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)) M.d) hstrict,
      geoStrictTransform_actual_preimage hf hπ hρ M.N,hnum,
      pullback_idealPow (actualLift_contMDiff hf hπ hρ)
        (isCoherent_pullback hπ.contMDiff (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)),
      actualLift_whole_ideal hf hπ hρ]
  · rfl

theorem IsActualTowerPullback.relative_marked_dictionary
    {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower M T) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q =
        markedPullback (m := m) g (geoTransformAlong M T) := by
  induction h with
  | refl => exact ⟨True.intro,rfl⟩
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    obtain ⟨hTT,hC⟩ := hT
    obtain ⟨hQT,hmark⟩ := ih hTT
    have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTT
    refine ⟨⟨hQT,?_⟩,?_⟩
    · rw [hmark]
      exact isAdmissibleCentre_markedPullback hg (geoTransformAlong M T) hMT.isCoherent hC
    · change (geoTransformAlong (markedPullback (m := m) f M) Q).geoTransform (g ⁻¹' C) ρ =
        markedPullback (m := m) (actualLift hg hπ hρ) ((geoTransformAlong M T).geoTransform C π)
      rw [hmark]
      exact markedPullback_geoTransform_actual_relative hg hπ hρ (geoTransformAlong M T) hMT hC

theorem IsActualTowerPullback.relative_cosupport_dictionary
    {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower M T) :
    (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp =
      g ⁻¹' (geoTransformAlong M T).cosupp := by
  rw [(IsActualTowerPullback.relative_marked_dictionary h M hM hT).2]
  exact cosupport_preimage_eq h.isSubmersion
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isCoherent
    (geoTransformAlong M T).N (geoTransformAlong M T).d

theorem exists_actual_relative_marked_tower {X D : CMfd.{u} n} {Y : CMfd.{u} m}
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      Q.length = T.length ∧ HolomorphicSquarePullback f g Q.proj T.proj ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q =
        markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).IsWellFormed ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp =
        g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ j : ℕ, ∃ k : (BlowupTowerSplit.split Q j).1 → (BlowupTowerSplit.split T j).1,
        IsActualTowerPullback f (BlowupTowerSplit.head Q j) (BlowupTowerSplit.head T j) k ∧
        Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ k ∧
        HolomorphicSquarePullback f k (BlowupTowerSplit.head Q j).proj
          (BlowupTowerSplit.head T j).proj ∧
        IsGeoTestTower (markedPullback (m := m) f M) (BlowupTowerSplit.head Q j) ∧
        geoTransformAlong (markedPullback (m := m) f M) (BlowupTowerSplit.head Q j) =
          markedPullback (m := m) k (geoTransformAlong M (BlowupTowerSplit.head T j)) ∧
        (geoTransformAlong (markedPullback (m := m) f M) (BlowupTowerSplit.head Q j)).IsWellFormed ∧
        (geoTransformAlong (markedPullback (m := m) f M) (BlowupTowerSplit.head Q j)).cosupp =
          k ⁻¹' (geoTransformAlong M (BlowupTowerSplit.head T j)).cosupp := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  have hMP := isWellFormed_markedPullback_submersion hf M hM
  obtain ⟨hQ,hmark⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM hT
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.universal,hQ,hmark,
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMP Q hQ,
    IsActualTowerPullback.relative_cosupport_dictionary h M hM hT,?_⟩
  intro j
  obtain ⟨k,hk⟩ := h.head j
  have hTH := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M T j).mp hT).1
  obtain ⟨hQH,hmarkH⟩ := IsActualTowerPullback.relative_marked_dictionary hk M hM hTH
  exact ⟨k,hk,hk.isSubmersion,hk.universal,hQH,hmarkH,
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMP _ hQH,
    IsActualTowerPullback.relative_cosupport_dictionary hk M hM hTH⟩

end
end Hironaka.HironakaSmoothSubmersionRelativeControlledTower
