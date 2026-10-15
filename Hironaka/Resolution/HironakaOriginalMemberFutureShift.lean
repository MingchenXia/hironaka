/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.MonomialInvariantEmptyMember
import Hironaka.Resolution.HironakaStepOneMemberHeadIncidence

/-!
Original positive lower boundary and future-only monomial insertion order.
The complete original-input Mathematics.tex and Blueprint.tex precede this source.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalMemberFutureShift
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  StepOneValue InvDomainMemberRestriction InvDomainRebase MonomialInvariant
  MonomialCase MonomialCaseAlong MonomialStepAlong MonomialInvariantEmptyMember HomogenizedGlueingTower
variable {n : ℕ} {X Y : CMfd.{u} n}


open Classical in
def retainedOriginalCount (m : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y) : ℕ :=
  ((origMembers m H).filter fun W => decide (p ∉ W)).length

theorem lowerMarked_succ_boundary_empty_prefix (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ) :
    ∃ F : List (Set (maskA m H p)),
      (lowerMarked m (s+1) H p).E =
        List.replicate (retainedOriginalCount m H p) ∅ ++ F := by
  classical
  let J := geoTransformAlong (barMarked m) H
  let E₀ := origMembers m H
  let P : Set Y → Bool := fun W => decide ¬ (W ∈ E₀ ∧ p ∈ W)
  let A := E₀.filter fun W => decide (p ∉ W)
  let F := (J.E.drop m.E.length).filter P
  have hsplit : J.E.filter P = A ++ F := by
    calc
      J.E.filter P = (J.E.take m.E.length ++ J.E.drop m.E.length).filter P :=
        congrArg (List.filter P) (List.take_append_drop m.E.length J.E).symm
      _ = A ++ F := by
        rw [List.filter_append]
        congr 1
        apply List.filter_congr
        intro W hW
        have hw₀ : W ∈ E₀ := hW
        simp only [P, hw₀, true_and]
  have hA : A.map ((Subtype.val : maskA m H p → Y) ⁻¹' ·) =
      List.replicate (retainedOriginalCount m H p) ∅ := by
    have he : ∀ W ∈ A, (Subtype.val : maskA m H p → Y) ⁻¹' W = ∅ := by
      intro W hW
      obtain ⟨hw₀, hpW⟩ := List.mem_filter.mp hW
      have hpW' : p ∉ W := of_decide_eq_true hpW
      ext z
      constructor
      · intro hz
        have hzdata : (∀ V ∈ E₀, (z : Y) ∈ V → p ∈ V) ∧
            ¬ (level m H (z : Y) = level m H p ∧ IsSpecial m H (z : Y)) :=
          @interior_subset Y _ {w : Y |
            (∀ V ∈ E₀, w ∈ V → p ∈ V) ∧
              ¬ (level m H w = level m H p ∧ IsSpecial m H w)} z.val z.property
        exact False.elim (hpW' (hzdata.1 W hw₀ hz))
      · intro hz
        exact False.elim hz
    calc
      A.map ((Subtype.val : maskA m H p → Y) ⁻¹' ·) = A.map (fun _ => (∅ : Set (maskA m H p))) :=
        List.map_congr_left he
      _ = List.replicate (retainedOriginalCount m H p) ∅ := by simp [retainedOriginalCount, A, E₀]
  refine ⟨F.map ((Subtype.val : maskA m H p → Y) ⁻¹' ·), ?_⟩
  change ((memberRestrict J (membersThrough J.E E₀ p)).E.map
    ((Subtype.val : maskA m H p → Y) ⁻¹' ·)) = _
  rw [memberRestrict_membersThrough_E]
  change (J.E.filter P).map _ = _
  rw [hsplit, List.map_append, hA]
  rfl


theorem empty_prefix_geoTransformAlong (m : MarkedIdeal n X) (j : ℕ)
    (hj : j ≤ m.E.length) (he : m.E.take j = List.replicate j ∅) :
    ∀ {Z : CMfd.{u} n} (T : BlowupTower X Z),
      (geoTransformAlong m T).E.take j = List.replicate j ∅
  | _, .refl => he
  | _, .step T C π hπ => by
    have hlen : j ≤ ((geoTransformAlong m T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C)).length := by
      rw [List.length_map, length_E_geoTransformAlong]
      omega
    rw [geoTransformAlong_step, geoTransform_E, List.take_append_of_le_length hlen,
      ← List.map_take, empty_prefix_geoTransformAlong m j hj he T]
    simp [BlowupStrictSubmanifold.geoStrictTransform]

theorem original_lower_tail_empty_prefix (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ)
    {Z : CMfd.{u} n} (R : BlowupTower (CMfd.of (n := n) (maskA m H p)) Z) :
    retainedOriginalCount m H p ≤ (geoTransformAlong (lowerMarked m (s+1) H p) R).E.length ∧
      (geoTransformAlong (lowerMarked m (s+1) H p) R).E.take (retainedOriginalCount m H p) =
        List.replicate (retainedOriginalCount m H p) ∅ := by
  let L : MarkedIdeal n (CMfd.of (n := n) (maskA m H p)) := lowerMarked m (s+1) H p
  obtain ⟨F,hE⟩ := lowerMarked_succ_boundary_empty_prefix m H p s
  change L.E = List.replicate (retainedOriginalCount m H p) ∅ ++ F at hE
  have hj : retainedOriginalCount m H p ≤ L.E.length := by
    rw [hE,List.length_append,List.length_replicate]
    omega
  have he : L.E.take (retainedOriginalCount m H p) =
      List.replicate (retainedOriginalCount m H p) ∅ := by
    rw [hE,List.take_append_of_le_length (by simp),List.take_replicate]
    simp
  change retainedOriginalCount m H p ≤ (geoTransformAlong L R).E.length ∧
    (geoTransformAlong L R).E.take (retainedOriginalCount m H p) = _
  refine ⟨?_,empty_prefix_geoTransformAlong L _ hj he R⟩
  rw [length_E_geoTransformAlong]
  omega

theorem memberIdx_ge_of_empty_prefix {E : List (Set Y)} {j : ℕ}
    (he : E.take j = List.replicate j ∅) (y : Y) :
    ∀ i ∈ memberIdx E y, j ≤ i := by
  intro i hi
  obtain ⟨hiE,hy⟩ := (mem_memberIdx E).mp hi
  by_contra hji
  have hij : i < j := by omega
  have hit : i < (E.take j).length := by simp only [List.length_take];omega
  have hget : (E.take j).get ⟨i,hit⟩ = E.get ⟨i,hiE⟩ := by
    simp [List.get_eq_getElem]
  have hmem : E.get ⟨i,hiE⟩ ∈ E.take j := by
    rw [← hget]
    exact List.get_mem _ _
  rw [he] at hmem
  obtain ⟨_,hempty⟩ := List.mem_replicate.mp hmem
  exact Set.notMem_empty y (hempty ▸ hy)

theorem gammaAlong_key_positions_ge_of_empty_prefix (N : Set Y) (I : GermIdeal n Y)
    (E : List (Set Y)) (d : ℕ) {j : ℕ}
    (he : E.take j = List.replicate j ∅) (y : Y) (v : Val)
    (hv : gammaAlong n N I E d y = (v : WithBot Val)) :
    ∀ i ∈ ofColex (ofLex (ofLex v).2).2, j ≤ i := by
  classical
  unfold gammaAlong inv at hv
  obtain ⟨K,hK,hKv⟩ := Finset.mem_image.mp (Finset.mem_of_max hv)
  subst v
  simp only [key,ofLex_toLex,ofColex_toColex]
  intro i hi
  exact memberIdx_ge_of_empty_prefix he y i ((mem_feasible.mp hK).1 hi)

theorem shiftSet_eq_shiftSet_zero_of_ge {j : ℕ} {K : Finset ℕ}
    (hK : ∀ i ∈ K, j ≤ i) : shiftSet j K = shiftSet 0 K := by
  unfold shiftSet
  apply Finset.image_congr
  intro i hi
  rw [shiftIdx_of_le (hK i hi),shiftIdx_of_le (Nat.zero_le i)]

theorem shiftVal_inv_eq_shiftVal_zero_of_ge (a : ℕ → ℕ) (d : ℕ)
    {S : Finset ℕ} {j : ℕ} (hS : ∀ i ∈ S, j ≤ i) :
    shiftVal j (inv n S a d) = shiftVal 0 (inv n S a d) := by
  by_cases hd : d ≤ ∑ i ∈ S, a i
  · obtain ⟨K,hK,hv,_⟩ := exists_top (n := n) hd
    have hk := shiftSet_eq_shiftSet_zero_of_ge
      (fun i hi => hS i ((mem_feasible.mp hK).1 hi))
    rw [hv,shiftVal_coe,shiftVal_coe]
    congr 1
    simp only [shiftKey,key,ofLex_toLex,ofColex_toColex]
    rw [hk]
  · rw [(inv_eq_bot_iff (n := n)).mpr (not_le.mp hd),shiftVal_bot,shiftVal_bot]

theorem gammaAlong_uniform_shift_of_empty_prefix (N : Set Y) (I : GermIdeal n Y)
    (E : List (Set Y)) (d : ℕ) {j : ℕ} (hj : j ≤ E.length)
    (he : E.take j = List.replicate j ∅) (y : Y) :
    gammaAlong n N I (E.insertIdx j ∅) d y = shiftVal 0 (gammaAlong n N I E d y) := by
  rw [gammaAlong_insertIdx_empty N I E hj d y]
  exact shiftVal_inv_eq_shiftVal_zero_of_ge _ _ (memberIdx_ge_of_empty_prefix he y)

theorem original_lower_towerInv_insertEmpty_uniform (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ)
    {Z : CMfd.{u} n} (R : BlowupTower (CMfd.of (n := n) (maskA m H p)) Z) (z : Z) :
    towerInvAlong (insertEmpty (retainedOriginalCount m H p) (lowerMarked m (s+1) H p)) R z =
      shiftVal 0 (towerInvAlong (lowerMarked m (s+1) H p) R z) := by
  let L : MarkedIdeal n (CMfd.of (n := n) (maskA m H p)) := lowerMarked m (s+1) H p
  obtain ⟨F,hE⟩ := lowerMarked_succ_boundary_empty_prefix m H p s
  change L.E = List.replicate (retainedOriginalCount m H p) ∅ ++ F at hE
  have hj : retainedOriginalCount m H p ≤ L.E.length := by
    rw [hE,List.length_append,List.length_replicate]
    omega
  change towerInvAlong (insertEmpty (retainedOriginalCount m H p) L) R z =
    shiftVal 0 (towerInvAlong L R z)
  unfold towerInvAlong
  rw [geoTransformAlong_insertEmpty L hj R]
  have hpref := original_lower_tail_empty_prefix m H p s R
  exact gammaAlong_uniform_shift_of_empty_prefix _ _ _ _ hpref.1 hpref.2 z


variable {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → Λ)

private theorem actual_lower_genInv_insertEmpty_of_order_zero (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ)
    {Z : CMfd.{u} n} (R : BlowupTower (CMfd.of (n := n) (maskA m H p)) Z) (z : Z)
    (hz : NonmonomialOrderLocal.nmOrd (geoTransformAlong (lowerMarked m (s+1) H p) R) z = 0) :
    GeneralValue.genInv M (insertEmpty (retainedOriginalCount m H p) (lowerMarked m (s+1) H p)) R z =
      toLex ((0 : ℕ), (toLex (Sum.inl (shiftVal 0 (towerInvAlong (lowerMarked m (s+1) H p) R z))) :
        WithBot Val ⊕ₗ WithTop Λ)) := by
  let L : MarkedIdeal n (CMfd.of (n := n) (maskA m H p)) := lowerMarked m (s+1) H p
  change NonmonomialOrderLocal.nmOrd (geoTransformAlong L R) z = 0 at hz
  change GeneralValue.genInv M (insertEmpty (retainedOriginalCount m H p) L) R z = _
  obtain ⟨F,hE⟩ := lowerMarked_succ_boundary_empty_prefix m H p s
  change L.E = List.replicate (retainedOriginalCount m H p) ∅ ++ F at hE
  have hj : retainedOriginalCount m H p ≤ L.E.length := by
    rw [hE,List.length_append,List.length_replicate]
    omega
  rw [GeneralValueOrderZero.genInv_eq_towerInvAlong M _ R
    ((nmOrd_geoTransformAlong_insertEmpty L hj R z).trans hz)]
  rw [original_lower_towerInv_insertEmpty_uniform m H p s R z]

theorem original_lower_zero_order_comparisons (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ)
    {Z : CMfd.{u} n} (R : BlowupTower (CMfd.of (n := n) (maskA m H p)) Z) (z : Z)
    {X' Y' Z' : CMfd.{u} n} (m' : MarkedIdeal n X') (H' : BlowupTower X' Y') (p' : Y') (s' : ℕ)
    (R' : BlowupTower (CMfd.of (n := n) (maskA m' H' p')) Z') (z' : Z')
    (hz : NonmonomialOrderLocal.nmOrd (geoTransformAlong (lowerMarked m (s+1) H p) R) z = 0)
    (hz' : NonmonomialOrderLocal.nmOrd (geoTransformAlong (lowerMarked m' (s'+1) H' p') R') z' = 0) :
    let v := GeneralValue.genInv M (lowerMarked m (s+1) H p) R z
    let w := GeneralValue.genInv M (lowerMarked m' (s'+1) H' p') R' z'
    let v' := GeneralValue.genInv M
      (insertEmpty (retainedOriginalCount m H p) (lowerMarked m (s+1) H p)) R z
    let w' := GeneralValue.genInv M
      (insertEmpty (retainedOriginalCount m' H' p') (lowerMarked m' (s'+1) H' p')) R' z'
    (v' < w' ↔ v < w) ∧ (v' ≤ w' ↔ v ≤ w) ∧ (v' = w' ↔ v = w) := by
  dsimp only
  rw [actual_lower_genInv_insertEmpty_of_order_zero M m H p s R z hz,
    actual_lower_genInv_insertEmpty_of_order_zero M m' H' p' s' R' z' hz',
    GeneralValueOrderZero.genInv_eq_towerInvAlong M _ R hz,
    GeneralValueOrderZero.genInv_eq_towerInvAlong M _ R' hz']
  have hstrict := strictMono_shiftVal 0
  simp [Prod.Lex.toLex_lt_toLex,Prod.Lex.toLex_le_toLex,hstrict.lt_iff_lt,hstrict.le_iff_le,hstrict.injective.eq_iff]

theorem original_lower_zero_order_maxLocus (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ)
    {Z : CMfd.{u} n} (R : BlowupTower (CMfd.of (n := n) (maskA m H p)) Z) (A : Set Z)
    (hz : ∀ z ∈ A, NonmonomialOrderLocal.nmOrd (geoTransformAlong (lowerMarked m (s+1) H p) R) z = 0) :
    ResolutionDriver.maxLocus
      (GeneralValue.genInv M (insertEmpty (retainedOriginalCount m H p) (lowerMarked m (s+1) H p)) R) A =
    ResolutionDriver.maxLocus (GeneralValue.genInv M (lowerMarked m (s+1) H p) R) A := by
  ext z
  constructor
  · rintro ⟨hzA,hmax⟩
    refine ⟨hzA,fun w hw => ?_⟩
    exact (original_lower_zero_order_comparisons M m H p s R w m H p s R z (hz w hw) (hz z hzA)).2.1.mp
      (hmax w hw)
  · rintro ⟨hzA,hmax⟩
    refine ⟨hzA,fun w hw => ?_⟩
    exact (original_lower_zero_order_comparisons M m H p s R w m H p s R z (hz w hw) (hz z hzA)).2.1.mpr
      (hmax w hw)

end
end Hironaka.HironakaOriginalMemberFutureShift
