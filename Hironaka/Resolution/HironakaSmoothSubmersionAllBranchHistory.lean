/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionRegularityReflection
import Hironaka.Resolution.HironakaSmoothSubmersionPositiveMemberHistory
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionAllBranchHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  StepOneValue StepOneLowerDomain StepOneRegime CodimOneSupportAlong
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionRegularityReflection

/-- Coherence and the original smooth map internally identify the whole
actual codimension-one support, with no regularity comparison certificate. -/
theorem codimOnePartAlong_preimage_eq {n m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) (N : Set X) (d : ℕ) :
    codimOnePartAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) d =
      f ⁻¹' codimOnePartAlong N I d := by
  unfold codimOnePartAlong
  rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hf hI N d]
  ext y
  exact regular_codim_one_preimage_iff (hf.isSubmersionAt y) N
    (GermIdealOrder.cosupport n N I d)

variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- The actual ORIGINAL stage supplies coherence and all codimension-one
geometry internally; the entire bar record stays literal. -/
theorem IsActualTowerPullback.bar_codimOne_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) :
    codimOnePartAlong (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).N
      (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).ideal
      (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).d =
      g ⁻¹' codimOnePartAlong (geoTransformAlong (barMarked M) T).N
        (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d := by
  have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM) T hT
  rw [(HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_stage_dictionary h M hM hT).2]
  exact codimOnePartAlong_preimage_eq h.isSubmersion hMT.isCoherent _ _

/-- The actual zero and positive special branches both retain the original
point predicate, without a positive-level premise. -/
theorem IsActualTowerPullback.all_isSpecial_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (z : D') :
    IsSpecial (markedPullback (m := m) f M) Q z ↔ IsSpecial M T (g z) := by
  unfold IsSpecial
  rw [HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_level_dictionary h M hM hT z,
    IsActualTowerPullback.bar_codimOne_dictionary h M hM hT,
    HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_member_locus_dictionary h M hM hT]
  rfl

/-- Every actual fixed-level regime, including zero, is the original one. -/
theorem IsActualTowerPullback.all_stepRegime_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (s : ℕ) (z : D') :
    stepRegime (markedPullback (m := m) f M) s Q z ↔ stepRegime M s T (g z) := by
  change (_ = s ∧ ¬ IsSpecial _ Q z) ↔ (_ = s ∧ ¬ IsSpecial M T (g z))
  rw [HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_level_dictionary h M hM hT z,
    IsActualTowerPullback.all_isSpecial_dictionary h M hM hT z]

/-- The entire literal run recursion is compared on true Cartesian histories
for every fixed level, with no run-equality premise. -/
theorem IsActualTowerPullback.all_stepRegime_run
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (s : ℕ) :
    ∀ z : D', regimeRun (stepRegime (markedPullback (m := m) f M) s) Q z =
      regimeRun (stepRegime M s) T (g z) := by
  classical
  induction h with
  | refl => intro z; rfl
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro z
    obtain ⟨hTT,_⟩ := hT
    have hp := IsActualTowerPullback.all_stepRegime_dictionary h M hM hTT s (ρ z)
    have hsquare : π (actualLift hg hπ hρ z) = g (ρ z) :=
      congrFun (actualLift_proj_comm hg hπ hρ) z
    rw [regimeRun_step,regimeRun_step,hsquare]
    by_cases hz : stepRegime M s T (g (ρ z))
    · rw [if_pos (hp.mpr hz),if_pos hz,ih hTT]
    · rw [if_neg (fun hh => hz (hp.mp hh)),if_neg hz]

/-- The genuine original member mask is the actual full smooth preimage at
all levels; no zero/positive branch restriction survives. -/
theorem IsActualTowerPullback.all_maskA_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (z : D') :
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
    rw [HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_original_members_dictionary h M hM hT]
    simp only [List.forall_mem_map,mem_preimage]
    change ((∀ H ∈ origMembers M T, g w ∈ H → g z ∈ H) ∧ _) ↔
      ((∀ H ∈ origMembers M T, g w ∈ H → g z ∈ H) ∧ _)
    rw [HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_level_dictionary h M hM hT w,
      HironakaSmoothSubmersionPositiveMemberHistory.IsActualTowerPullback.bar_level_dictionary h M hM hT z,
      IsActualTowerPullback.all_isSpecial_dictionary h M hM hT w]
  change interior B = g ⁻¹' interior A
  rw [hAB]
  have hgOpen := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion h.isSubmersion
  exact (hgOpen.preimage_interior_eq_interior_preimage h.isSubmersion.contMDiff.continuous A).symm
end
end Hironaka.HironakaSmoothSubmersionAllBranchHistory
