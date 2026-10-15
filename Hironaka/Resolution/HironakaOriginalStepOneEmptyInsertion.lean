/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.MonomialInvariantEmptyMember
import Hironaka.Invariant.GeneralEmptyPrefix
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOneEmptyInsertion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  StepOneValue StepOneRegime StepOneEmptyPrefix MonomialInvariantEmptyMember
  MonomialCase BoundaryCount MemberInterLocusAlong HomogenizedGlueingTower CodimOneSupportAlong
  MarkedIdealBiholomorphism
variable {n : ℕ} {X Y : CMfd.{u} n}


theorem barMarked_insertEmpty (m : MarkedIdeal n X) (j : ℕ) :
    barMarked (insertEmpty j m) = insertEmpty j (barMarked m) := rfl

theorem bar_geoTransformAlong_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) :
    geoTransformAlong (barMarked (insertEmpty j m)) T =
      insertEmpty j (geoTransformAlong (barMarked m) T) := by
  rw [barMarked_insertEmpty]
  exact geoTransformAlong_insertEmpty (barMarked m) hj T

theorem origMembers_insertEmpty (m : MarkedIdeal n X) (j : ℕ) (T : BlowupTower X Y) :
    origMembers (insertEmpty j m) T = (origMembers m T).insertIdx j ∅ := by
  rw [origMembers_eq,origMembers_eq]
  change (m.E.insertIdx j ∅).map (strictAlong T) = (m.E.map (strictAlong T)).insertIdx j ∅
  rw [List.map_insertIdx,strictAlong_empty]

theorem boundaryCount_insertIdx_empty (E : List (Set Y)) {j : ℕ}
    (hj : j ≤ E.length) (y : Y) : boundaryCount (E.insertIdx j ∅) y = boundaryCount E y := by
  have hc := congrArg Finset.card (memberIdx_insertIdx_empty E hj y)
  simpa only [memberIdx,Finset.card_map,card_shiftSet,boundaryCount] using hc

theorem memberInterLocus_insertIdx_empty (N A : Set Y) (E : List (Set Y))
    {j : ℕ} (hj : j ≤ E.length) :
    memberInterLocus N (E.insertIdx j ∅) A = memberInterLocus N E A := by
  ext x
  rw [mem_memberInterLocus_iff,mem_memberInterLocus_iff]
  refine and_congr Iff.rfl (eventually_congr (Eventually.of_forall fun y => ?_))
  apply imp_congr_right
  intro _
  apply imp_congr_left
  rw [← forall_get_iff,← forall_get_iff]
  exact forall_get_insertIdx_empty_iff E hj (Q := fun W : Set Y => x ∈ W → y ∈ W) (fun hx => False.elim (Set.notMem_empty x hx))

theorem level_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) (y : Y) :
    level (insertEmpty j m) T y = level m T y := by
  unfold level
  rw [origMembers_insertEmpty m j T]
  apply boundaryCount_insertIdx_empty
  rw [origMembers_eq,List.length_map]
  exact hj

theorem isSpecial_insertEmpty_iff (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) (y : Y) :
    IsSpecial (insertEmpty j m) T y ↔ IsSpecial m T y := by
  unfold IsSpecial
  rw [level_insertEmpty m hj T,bar_geoTransformAlong_insertEmpty m hj T,
    origMembers_insertEmpty m j T]
  dsimp only [insertEmpty]
  rw [memberInterLocus_insertIdx_empty _ _ _ (by rw [origMembers_eq,List.length_map];exact hj)]
  rfl


theorem tangentChoice_insertEmpty (m : MarkedIdeal n X) (j : ℕ) (x : X) :
    tangentChoice (insertEmpty j m) x = tangentChoice m x := rfl

theorem maskA_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) (p : Y) :
    maskA (insertEmpty j m) T p = maskA m T p := by
  apply Opens.ext
  change interior {z : Y | (∀ W ∈ origMembers (insertEmpty j m) T, z ∈ W → p ∈ W) ∧
    ¬ (level (insertEmpty j m) T z = level (insertEmpty j m) T p ∧ IsSpecial (insertEmpty j m) T z)} = _
  congr 1
  ext z
  simp only [mem_ofPred_eq]
  rw [origMembers_insertEmpty m j T,level_insertEmpty m hj T z,
    level_insertEmpty m hj T p,isSpecial_insertEmpty_iff m hj T z]
  apply and_congr_left
  intro _
  rw [← forall_get_iff,← forall_get_iff]
  exact forall_get_insertIdx_empty_iff _ (by rw [origMembers_eq,List.length_map];exact hj)
    (Q := fun W : Set Y => z ∈ W → p ∈ W) (fun hz => False.elim (Set.notMem_empty z hz))

theorem maskB_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) (p : Y) :
    maskB (insertEmpty j m) T p = maskB m T p := by
  apply Opens.ext
  change interior {z : Y | T.proj z ∈ (tangentChoice (insertEmpty j m) (T.proj p)).1 ∧
    (∀ W ∈ origMembers (insertEmpty j m) T, z ∉ W) ∧
      z ∉ codimOnePartAlong (geoTransformAlong (barMarked (insertEmpty j m)) T).N
        (geoTransformAlong (barMarked (insertEmpty j m)) T).ideal
        (geoTransformAlong (barMarked (insertEmpty j m)) T).d} = _
  congr 1
  ext z
  simp only [mem_ofPred_eq]
  rw [tangentChoice_insertEmpty,origMembers_insertEmpty m j T,
    bar_geoTransformAlong_insertEmpty m hj T]
  dsimp only [insertEmpty]
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  rw [← forall_get_iff,← forall_get_iff]
  exact forall_get_insertIdx_empty_iff _ (by rw [origMembers_eq,List.length_map];exact hj)
    (Q := fun W : Set Y => z ∉ W) (Set.notMem_empty z)

private theorem contactMarked_heq_of_equal_masks (N : Set X)
    (I : GermIdeal n X) (d : ℕ) (w : X → ℂ) (T : BlowupTower X Y)
    (U V : Opens Y) (hUV : U = V) :
    HEq (MaximalOrderStepOneB.contactMarked N I d w T U)
      (MaximalOrderStepOneB.contactMarked N I d w T V) := by
  subst V
  rfl

theorem lowerMarked_zero_insertEmpty_heq (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) (p : Y) :
    HEq (lowerMarked (insertEmpty j m) 0 T p) (lowerMarked m 0 T p) := by
  unfold lowerMarked
  rw [tangentChoice_insertEmpty]
  exact contactMarked_heq_of_equal_masks m.N m.ideal m.d _ T _ _ (maskB_insertEmpty m hj T p)

theorem stepRegime_insertEmpty_iff (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    stepRegime (insertEmpty j m) s T y ↔ stepRegime m s T y := by
  unfold stepRegime
  rw [level_insertEmpty m hj T,isSpecial_insertEmpty_iff m hj T]

theorem regimeRun_stepRegime_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (s : ℕ) :
    ∀ {Z : CMfd.{u} n} (T : BlowupTower X Z) (z : Z),
      regimeRun (stepRegime (insertEmpty j m) s) T z = regimeRun (stepRegime m s) T z
  | _, .refl, _ => rfl
  | _, .step T C π hπ, z => by
    rw [regimeRun_step,regimeRun_step]
    have hq := stepRegime_insertEmpty_iff m hj s T (π z)
    by_cases h : stepRegime m s T (π z)
    · rw [if_pos (hq.mpr h),if_pos h,regimeRun_stepRegime_insertEmpty m hj s T (π z)]
    · rw [if_neg (fun hi => h (hq.mp hi)),if_neg h]


private theorem pullback_insertEmpty_heq_of_equal_masks (J : MarkedIdeal n Y)
    (j : ℕ) (U V : Opens Y) (hUV : U = V) :
    HEq (MarkedIdeal.pullback (Subtype.val : U → Y) (insertEmpty j J))
      (insertEmpty j (MarkedIdeal.pullback (Subtype.val : V → Y) J)) := by
  subst V
  apply heq_of_eq
  change MarkedIdeal.mk _ ((J.E.insertIdx j ∅).map ((Subtype.val : U → Y) ⁻¹' ·)) _ _ =
    MarkedIdeal.mk _ ((J.E.map ((Subtype.val : U → Y) ⁻¹' ·)).insertIdx j ∅) _ _
  rw [List.map_insertIdx,Set.preimage_empty]
  rfl

theorem lowerMarkedB_insertEmpty_heq (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (T : BlowupTower X Y) (p : Y) :
    HEq (StepOneValueMasked.lowerMarkedB (insertEmpty j m) T p)
      (insertEmpty j (StepOneValueMasked.lowerMarkedB m T p)) := by
  let J := CoefficientIdealRestriction.withN
    (HomogenizedIdealAlong.coeffMarkedAlong (geoTransformAlong (barMarked m) T))
    (strictAlong T (m.N ∩ {x | (tangentChoice m (T.proj p)).2 x = 0}))
  have hraw : CoefficientIdealRestriction.withN
      (HomogenizedIdealAlong.coeffMarkedAlong (geoTransformAlong (barMarked (insertEmpty j m)) T))
      (strictAlong T ((insertEmpty j m).N ∩ {x | (tangentChoice (insertEmpty j m) (T.proj p)).2 x = 0})) =
      insertEmpty j J := by
    rw [bar_geoTransformAlong_insertEmpty m hj T,tangentChoice_insertEmpty]
    rfl
  unfold StepOneValueMasked.lowerMarkedB
  rw [hraw]
  exact pullback_insertEmpty_heq_of_equal_masks J j _ _ (maskB_insertEmpty m hj T p)

end
end Hironaka.HironakaOriginalStepOneEmptyInsertion
