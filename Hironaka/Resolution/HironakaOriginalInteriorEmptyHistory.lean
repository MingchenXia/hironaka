/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.BlowupEmptyIdentityExact
import Hironaka.Support.CodimOneRestrictedTowerExact
import Hironaka.Resolution.HironakaOriginalInvariantEmptyInsertion
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Actual identity empty steps in the middle of the SAME original history.
The complete mathematical producer and proofs were written first in
`hironaka-original-interior-empty-history-extension.tex`. Full recursive value deletion and noncompact scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalInteriorEmptyHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MonomialInvariantEmptyMember MarkedIdealBiholomorphism StepOneValue StepOneLowerDomain
  CodimOneSupportAlong CodimOnePartCanonical HironakaCoherentTransformExtension
open MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
variable {n : ℕ} {X A Y : CMfd.{u} n}

def interiorEmptyHistory (H : BlowupTower X A) (S : BlowupTower A Y) : BlowupTower X Y :=
  (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty).append S

theorem proj_interiorEmptyHistory (H : BlowupTower X A) (S : BlowupTower A Y) :
    (interiorEmptyHistory H S).proj = (H.append S).proj := by
  rw [interiorEmptyHistory,BlowupTower.proj_append,BlowupTower.proj_append,
    BlowupTower.proj_step,Function.comp_id]

theorem length_interiorEmptyHistory (H : BlowupTower X A) (S : BlowupTower A Y) :
    (interiorEmptyHistory H S).length = H.length + 1 + S.length := by
  rw [interiorEmptyHistory,BlowupTower.length_append,BlowupTower.length_step]

private theorem actual_empty_base (K : MarkedIdeal n A) (hK : K.IsWellFormed) :
    RestrictEquiv (emptyStepBase K id) K ∧ (emptyStepBase K id).ideal.IsCoherent := by
  have hr := restrictEquiv_emptyStepBase_pullback K BlowupExistenceCodimOne.isBlowupAlong_id_empty
    hK.isClosedSubmanifold_N.1 hK.isSNCDivisor.1
  rw [ContactCanonicalAlong.pullback_id K hK.isCoherent] at hr
  exact ⟨hr,(GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hK
    (isAdmissibleCentre_empty K) BlowupExistenceCodimOne.isBlowupAlong_id_empty).isCoherent⟩

/-- Actual carrier, entire ordered boundary, mark, cosupport and codimension-one
part for every tail; no admissibility of the tail is assumed. -/
theorem geometric_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) :
    (geoTransformAlong M (interiorEmptyHistory H S)).N = (geoTransformAlong M (H.append S)).N ∧
    (geoTransformAlong M (interiorEmptyHistory H S)).E =
      (geoTransformAlong M (H.append S)).E.insertIdx (M.E.length + H.length) ∅ ∧
    (geoTransformAlong M (interiorEmptyHistory H S)).d = (geoTransformAlong M (H.append S)).d ∧
    (geoTransformAlong M (interiorEmptyHistory H S)).cosupp = (geoTransformAlong M (H.append S)).cosupp ∧
    codimOnePartAlong (geoTransformAlong M (interiorEmptyHistory H S)).N
        (geoTransformAlong M (interiorEmptyHistory H S)).ideal
        (geoTransformAlong M (interiorEmptyHistory H S)).d =
      codimOnePartAlong (geoTransformAlong M (H.append S)).N
        (geoTransformAlong M (H.append S)).ideal (geoTransformAlong M (H.append S)).d := by
  have hK := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM H hH
  obtain ⟨hr,hB⟩ := actual_empty_base (geoTransformAlong M H) hK
  have hBN : IsClosed (emptyStepBase (geoTransformAlong M H) id).N := by
    rw [hr.N_eq]
    exact hK.isClosedSubmanifold_N.1
  rw [interiorEmptyHistory,geoTransformAlong_step_empty_append,geoTransformAlong_append]
  refine ⟨geoTransformAlong_N_eq_of_N_eq hr.N_eq S,?_,?_,?_,?_⟩
  · exact congrArg (fun E : List (Set Y) => E.insertIdx (M.E.length + H.length) ∅)
      (geoTransformAlong_E_eq_of_E_eq hr.E_eq S)
  · simp only [insertEmpty,d_geoTransformAlong,emptyStepBase,geoTransform_d]
  · exact (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
      hr hBN hB hK.isCoherent S).1
  · exact codimOnePartAlong_geoTransformAlong_of_restrictEquiv hr hBN hB hK.isCoherent S

/-- After at least one genuine tail step even the ambient ideal records agree
literally, with only the actual empty exceptional entry inserted. -/
theorem whole_record_of_nonempty_tail (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y)
    (hS : 0 < S.length) :
    geoTransformAlong M (interiorEmptyHistory H S) =
      insertEmpty (M.E.length + H.length) (geoTransformAlong M (H.append S)) := by
  have hK := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM H hH
  obtain ⟨hr,hB⟩ := actual_empty_base (geoTransformAlong M H) hK
  have hBN : IsClosed (emptyStepBase (geoTransformAlong M H) id).N := by
    rw [hr.N_eq]
    exact hK.isClosedSubmanifold_N.1
  rw [interiorEmptyHistory,geoTransformAlong_step_empty_append,geoTransformAlong_append]
  cases S with
  | refl => exact False.elim (Nat.lt_irrefl 0 hS)
  | step S C π hπ =>
    rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq
      hr hBN hB hK.isCoherent S C π hπ]

/-- The original boundary prefix retains every index, including when the tail is empty. -/
theorem original_members_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y) :
    origMembers M (interiorEmptyHistory H S) = origMembers M (H.append S) := by
  unfold origMembers
  rw [(geometric_dictionary (barMarked M) (isWellFormed_barMarked M hM) H hH S).2.1]
  exact List.take_insertIdx_eq_take_of_le _ _ _ _ (by
    change M.E.length ≤ M.E.length + H.length
    omega)

theorem level_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y) (y : Y) :
    level M (interiorEmptyHistory H S) y = level M (H.append S) y := by
  unfold level
  rw [original_members_dictionary M hM H hH S]

/-- Includes the actual zero-boundary codimension-one branch. -/
theorem isSpecial_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y) (y : Y) :
    IsSpecial M (interiorEmptyHistory H S) y ↔ IsSpecial M (H.append S) y := by
  have hh := geometric_dictionary (barMarked M) (isWellFormed_barMarked M hM) H hH S
  unfold IsSpecial
  rw [level_dictionary M hM H hH S y,hh.2.2.2.2,hh.1,
    original_members_dictionary M hM H hH S,hh.2.2.2.1]

theorem stepRegime_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (s : ℕ) (y : Y) :
    StepOneValue.stepRegime M s (interiorEmptyHistory H S) y ↔
      StepOneValue.stepRegime M s (H.append S) y := by
  unfold StepOneValue.stepRegime
  rw [level_dictionary M hM H hH S y,isSpecial_dictionary M hM H hH S y]

/-- Actual open member mask, with no pointwise positive-level restriction. -/
theorem maskA_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y) (p : Y) :
    maskA M (interiorEmptyHistory H S) p = maskA M (H.append S) p := by
  apply TopologicalSpace.Opens.ext
  unfold maskA
  simp only [original_members_dictionary M hM H hH S,level_dictionary M hM H hH S,
    isSpecial_dictionary M hM H hH S]

/-- The original tangentChoice has literally the same input, because the same
initial marked ideal and the same composite projection have been retained. -/
theorem maskB_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y) (p : Y) :
    maskB M (interiorEmptyHistory H S) p = maskB M (H.append S) p := by
  have hh := geometric_dictionary (barMarked M) (isWellFormed_barMarked M hM) H hH S
  apply TopologicalSpace.Opens.ext
  unfold maskB
  simp only [proj_interiorEmptyHistory H S,original_members_dictionary M hM H hH S,hh.2.2.2.2]

theorem lowerMask_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (s : ℕ) (p : Y) :
    lowerMask M s (interiorEmptyHistory H S) p = lowerMask M s (H.append S) p := by
  cases s with
  | zero => exact maskB_dictionary M hM H hH S p
  | succ s => exact maskA_dictionary M hM H hH S p

open Classical in
/-- The exact original fixed-regime run: an interior empty step adds one only
when the old run reaches that stage and that stage itself belongs to the regime. -/
theorem stepRegime_run_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (s : ℕ) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower A Y) (y : Y),
      let r := StepOneRegime.regimeRun (stepRegime M s) (H.append S) y
      StepOneRegime.regimeRun (stepRegime M s) (interiorEmptyHistory H S) y =
        if r < S.length then r else
          if stepRegime M s H (S.proj y) then r + 1 else S.length
  | _, .refl, y => by
    classical
    change (if stepRegime M s H y then StepOneRegime.regimeRun (stepRegime M s) H y + 1 else 0) =
      (if StepOneRegime.regimeRun (stepRegime M s) H y < 0 then _ else
        if stepRegime M s H y then _ else 0)
    simp only [Nat.not_lt_zero,if_false,BlowupTower.append_refl]
  | _, .step S C π hπ, y => by
    classical
    dsimp only
    change (if stepRegime M s (interiorEmptyHistory H S) (π y) then
        StepOneRegime.regimeRun (stepRegime M s) (interiorEmptyHistory H S) (π y) + 1 else 0) =
      (if (if stepRegime M s (H.append S) (π y) then
          StepOneRegime.regimeRun (stepRegime M s) (H.append S) (π y) + 1 else 0) < S.length + 1 then
        (if stepRegime M s (H.append S) (π y) then
          StepOneRegime.regimeRun (stepRegime M s) (H.append S) (π y) + 1 else 0) else
        if stepRegime M s H (S.proj (π y)) then
          (if stepRegime M s (H.append S) (π y) then
            StepOneRegime.regimeRun (stepRegime M s) (H.append S) (π y) + 1 else 0) + 1 else S.length + 1)
    simp only [stepRegime_dictionary M hM H hH S]
    by_cases hp : stepRegime M s (H.append S) (π y)
    · simp only [hp,if_true]
      rw [stepRegime_run_dictionary M hM H hH s S (π y)]
      split_ifs <;> omega
    · simp only [hp,if_false,Nat.zero_lt_succ,if_true]

end
end Hironaka.HironakaOriginalInteriorEmptyHistory
