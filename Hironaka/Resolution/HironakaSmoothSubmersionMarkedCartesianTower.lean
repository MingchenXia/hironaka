/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionControlledTransform
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionMarkedCartesianTower
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionControlledTransform
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionBlowupLift MarkedIdeals MarkedIdeals.MarkedIdeal
noncomputable section
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem IsActualTowerPullback.fullAmbient_marked_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : M.N = univ) (hT : IsGeoTestTower M T) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q =
        markedPullback (m := m) g (geoTransformAlong M T) := by
  induction h with
  | refl => exact ⟨True.intro,rfl⟩
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    obtain ⟨hTT,hC⟩ := hT
    obtain ⟨hQT,hmark⟩ := ih hTT
    have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTT
    have hNT := (pullback_eq_mul_geoTransformAlong M hN hM.isCoherent T hTT).1
    refine ⟨⟨hQT,?_⟩,?_⟩
    · rw [hmark]
      exact isAdmissibleCentre_markedPullback hg (geoTransformAlong M T) hMT.isCoherent hC
    · change (geoTransformAlong (markedPullback (m := m) f M) Q).geoTransform (g ⁻¹' C) ρ =
        markedPullback (m := m) (actualLift hg hπ hρ) ((geoTransformAlong M T).geoTransform C π)
      rw [hmark]
      exact markedPullback_geoTransform_actual hg hπ hρ (geoTransformAlong M T) hMT.isCoherent hNT hC

theorem IsActualTowerPullback.fullAmbient_cosupport_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : M.N = univ) (hT : IsGeoTestTower M T) :
    (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp =
      g ⁻¹' (geoTransformAlong M T).cosupp := by
  rw [(IsActualTowerPullback.fullAmbient_marked_dictionary h M hM hN hT).2]
  exact cosupport_preimage_eq h.isSubmersion
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isCoherent
    (geoTransformAlong M T).N (geoTransformAlong M T).d

theorem exists_actual_fullAmbient_marked_tower {X D : CMfd.{u} n} {Y : CMfd.{u} m}
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
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
  obtain ⟨hQ,hmark⟩ := IsActualTowerPullback.fullAmbient_marked_dictionary h M hM hN hT
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.universal,hQ,hmark,
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMP Q hQ,
    IsActualTowerPullback.fullAmbient_cosupport_dictionary h M hM hN hT,?_⟩
  intro j
  obtain ⟨k,hk⟩ := h.head j
  have hTH := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M T j).mp hT).1
  obtain ⟨hQH,hmarkH⟩ := IsActualTowerPullback.fullAmbient_marked_dictionary hk M hM hN hTH
  exact ⟨k,hk,hk.isSubmersion,hk.universal,hQH,hmarkH,
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMP _ hQH,
    IsActualTowerPullback.fullAmbient_cosupport_dictionary hk M hM hN hTH⟩

theorem exists_actual_fullAmbient_resolution_pullback {X D : CMfd.{u} n} {Y : CMfd.{u} m}
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (T : BlowupTower X D) (hT : IsGeoResolution M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      Q.length = T.length ∧ HolomorphicSquarePullback f g Q.proj T.proj ∧
      IsGeoResolution (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q =
        markedPullback (m := m) g (geoTransformAlong M T) := by
  obtain ⟨D',Q,g,h,hg,hL,hcart,hQ,hmark,hW,hCS,_⟩ :=
    exists_actual_fullAmbient_marked_tower hf M hM hN T hT.1
  refine ⟨D',Q,g,h,hg,hL,hcart,⟨hQ,?_⟩,hmark⟩
  rw [hCS,hT.2,preimage_empty]

end
end Hironaka.HironakaSmoothSubmersionMarkedCartesianTower
