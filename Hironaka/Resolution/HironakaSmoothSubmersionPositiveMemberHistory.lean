/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionHistoricalControlledTail
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeDifferentialIdeals
/-! # Actual positive Step-One member histories under smooth pullback

The literal original coefficient-homogenized record, indexed original members,
positive special branch, fixed positive regime runs and actual open member mask
are compared along actual Cartesian test histories. The zero-boundary
codimension-one branch, chosen contact masks, and complete higher recursive
invariant comparison remain open.

Blueprint: `hironaka-smooth-submersion-positive-member-history-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionPositiveMemberHistory
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativeDifferentialIdeals HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionNonmonomialHistory HironakaSmoothSubmersionOrder
  HomogenizedIdealAlong CoefficientIdealRestriction MemberInterLocusAlong StepOneRegime
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionMonomialOrdering
noncomputable section
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private theorem IsActualTowerPullback.base_submersion
    (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem pullback_barMarked
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) :
    markedPullback (m := m) f (barMarked M) = barMarked (markedPullback (m := m) f M) := by
  unfold barMarked
  rw [pullback_coeffMarkedAlong hf (homMarkedAlong M)
    (isCoherent_homMarkedAlong hM.isCoherent hM.isClosedSubmanifold_N)
    hM.isClosedSubmanifold_N,
    pullback_homMarkedAlong hf M hM.isCoherent hM.isClosedSubmanifold_N]

theorem IsActualTowerPullback.bar_stage_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) :
    IsGeoTestTower (barMarked (markedPullback (m := m) f M)) Q ∧
      geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q =
        markedPullback (m := m) g (geoTransformAlong (barMarked M) T) := by
  have hh := IsActualTowerPullback.relative_marked_dictionary h (barMarked M)
    (isWellFormed_barMarked M hM) hT
  rwa [pullback_barMarked (IsActualTowerPullback.base_submersion h) M hM] at hh

private theorem origMembers_barMarked (M : MarkedIdeal n X) (T : BlowupTower X D) :
    origMembers (barMarked M) T = origMembers M T := by
  simp only [origMembers_eq,barMarked_E]

theorem IsActualTowerPullback.bar_original_members_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) :
    origMembers (markedPullback (m := m) f M) Q = (origMembers M T).map (g ⁻¹' ·) := by
  calc
    _ = origMembers (barMarked (markedPullback (m := m) f M)) Q :=
      (origMembers_barMarked _ _).symm
    _ = origMembers (markedPullback (m := m) f (barMarked M)) Q := by
      rw [pullback_barMarked (IsActualTowerPullback.base_submersion h) M hM]
    _ = (origMembers (barMarked M) T).map (g ⁻¹' ·) :=
      IsActualTowerPullback.original_members_dictionary h (barMarked M)
        (isWellFormed_barMarked M hM) hT
    _ = _ := by rw [origMembers_barMarked]

theorem IsActualTowerPullback.bar_level_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (z : D') :
    level (markedPullback (m := m) f M) Q z = level M T (g z) := by
  unfold level
  rw [IsActualTowerPullback.bar_original_members_dictionary h M hM hT]
  exact CodimOnePartCanonical.boundaryCount_map_preimage g _ z

theorem IsActualTowerPullback.bar_member_locus_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) :
    memberInterLocus (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).N
      (origMembers (markedPullback (m := m) f M) Q)
      (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).cosupp =
    g ⁻¹' memberInterLocus (geoTransformAlong (barMarked M) T).N (origMembers M T)
      (geoTransformAlong (barMarked M) T).cosupp := by
  have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM) T hT
  rw [(IsActualTowerPullback.bar_stage_dictionary h M hM hT).2,
    IsActualTowerPullback.bar_original_members_dictionary h M hM hT]
  change memberInterLocus (g ⁻¹' (geoTransformAlong (barMarked M) T).N)
    ((origMembers M T).map (g ⁻¹' ·))
    (GermIdealOrder.cosupport m (g ⁻¹' (geoTransformAlong (barMarked M) T).N)
      (Hironaka.HolomorphicIdealSheaves.GermIdeal.pullback (m := m) g
        (geoTransformAlong (barMarked M) T).ideal) (geoTransformAlong (barMarked M) T).d) = _
  rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq h.isSubmersion
      hMT.isCoherent (geoTransformAlong (barMarked M) T).N
      (geoTransformAlong (barMarked M) T).d]
  exact memberInterLocus_preimage g
    (fun z => HironakaSmoothSubmersionDivisorExponents.map_nhds_submersion_eq
      (h.isSubmersion.isSubmersionAt z)) _ _ _

theorem IsActualTowerPullback.positive_isSpecial_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (z : D')
    (hpos : 1 ≤ level M T (g z)) :
    IsSpecial (markedPullback (m := m) f M) Q z ↔ IsSpecial M T (g z) := by
  have hz : level M T (g z) ≠ 0 := Nat.ne_of_gt hpos
  simp only [IsSpecial,IsActualTowerPullback.bar_level_dictionary h M hM hT z,
    hz,false_and,false_or,hpos,true_and]
  rw [IsActualTowerPullback.bar_member_locus_dictionary h M hM hT]
  rfl

theorem IsActualTowerPullback.positive_stepRegime_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T)
    (s : ℕ) (hs : 1 ≤ s) (z : D') :
    stepRegime (markedPullback (m := m) f M) s Q z ↔ stepRegime M s T (g z) := by
  change (_ = s ∧ ¬ IsSpecial _ Q z) ↔ (_ = s ∧ ¬ IsSpecial M T (g z))
  rw [IsActualTowerPullback.bar_level_dictionary h M hM hT z]
  apply and_congr_right
  intro he
  exact not_congr (IsActualTowerPullback.positive_isSpecial_dictionary h M hM hT z
    (he.symm ▸ hs))

theorem IsActualTowerPullback.positive_stepRegime_run
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T)
    (s : ℕ) (hs : 1 ≤ s) :
    ∀ z : D', regimeRun (stepRegime (markedPullback (m := m) f M) s) Q z =
      regimeRun (stepRegime M s) T (g z) := by
  classical
  induction h with
  | refl => intro z; rfl
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro z
    obtain ⟨hTT,_⟩ := hT
    have hp := IsActualTowerPullback.positive_stepRegime_dictionary h M hM hTT s hs (ρ z)
    have hsquare : π (actualLift hg hπ hρ z) = g (ρ z) :=
      congrFun (actualLift_proj_comm hg hπ hρ) z
    rw [regimeRun_step,regimeRun_step,hsquare]
    by_cases hz : stepRegime M s T (g (ρ z))
    · rw [if_pos (hp.mpr hz),if_pos hz,ih hTT]
    · rw [if_neg (fun hh => hz (hp.mp hh)),if_neg hz]

theorem IsActualTowerPullback.positive_maskA_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T)
    (z : D') (hpos : 1 ≤ level M T (g z)) :
    (maskA (markedPullback (m := m) f M) Q z : Set D') =
      g ⁻¹' (maskA M T (g z) : Set D) := by
  let A : Set D := {w | (∀ H ∈ origMembers M T, w ∈ H → g z ∈ H) ∧
    ¬ (level M T w = level M T (g z) ∧ IsSpecial M T w)}
  let B : Set D' := {w | (∀ H ∈ origMembers (markedPullback (m := m) f M) Q,
    w ∈ H → z ∈ H) ∧ ¬ (level (markedPullback (m := m) f M) Q w =
      level (markedPullback (m := m) f M) Q z ∧ IsSpecial (markedPullback (m := m) f M) Q w)}
  have hAB : B = g ⁻¹' A := by
    ext w
    change ((∀ H ∈ origMembers (markedPullback (m := m) f M) Q, w ∈ H → z ∈ H) ∧ _) ↔ _
    rw [IsActualTowerPullback.bar_original_members_dictionary h M hM hT]
    simp only [List.forall_mem_map,mem_preimage]
    change ((∀ H ∈ origMembers M T, g w ∈ H → g z ∈ H) ∧ _) ↔
      ((∀ H ∈ origMembers M T, g w ∈ H → g z ∈ H) ∧ _)
    rw [IsActualTowerPullback.bar_level_dictionary h M hM hT w,
      IsActualTowerPullback.bar_level_dictionary h M hM hT z]
    apply and_congr_right
    intro _
    apply not_congr
    apply and_congr_right
    intro he
    exact IsActualTowerPullback.positive_isSpecial_dictionary h M hM hT w (he.symm ▸ hpos)
  change interior B = g ⁻¹' interior A
  rw [hAB]
  have hgOpen := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion h.isSubmersion
  exact (hgOpen.preimage_interior_eq_interior_preimage h.isSubmersion.contMDiff.continuous A).symm
end
end Hironaka.HironakaSmoothSubmersionPositiveMemberHistory
