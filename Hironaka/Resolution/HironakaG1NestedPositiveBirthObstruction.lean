import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG11InvBMEmptyMemberStep
import Hironaka.Resolution.HironakaPrincipalizationBoundary

/-! Incident births in a restarted positive recursive companion. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1NestedPositiveBirthObstruction

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism StepOneValue StepOneValueMasked BoundaryCount
  InvDomainMemberRestriction InvDomainRebase NonmonomialOrderTail GeneralValue
  CompanionRebase CompanionReductionAlong HironakaG11InvBMEmptyMemberStep
  ResolutionInvariantSpec ResolutionInvariantExt BlowupStrictSubmanifold
  CanonicalCentres NonmonomialOrderLocal HironakaG1LaterPositiveSuccessorRead
  HironakaG1InitialPositiveGeneralRead HironakaPrincipalizationBoundary

open Classical in
private theorem selected_incident_slots {Y : Type} (E : List (Set Y)) (k : ℕ) (x : Y) :
    ((E.filter fun D => decide ¬ (D ∈ E.take k ∧ x ∈ D)).filter fun D => decide (x ∈ D)) =
      (E.drop k).filter (fun D => decide (x ∈ D ∧ D ∉ E.take k)) := by
  rw [List.filter_filter]
  have hEq : E.filter (fun D => decide (x ∈ D) && decide ¬ (D ∈ E.take k ∧ x ∈ D)) =
      E.filter (fun D => decide (x ∈ D ∧ D ∉ E.take k)) := by
    apply List.filter_congr
    intro D _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  rw [hEq]
  have hSplit : E = E.take k ++ E.drop k := (List.take_append_drop k E).symm
  have hOld : (E.take k).filter (fun D => decide (x ∈ D ∧ D ∉ E.take k)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro D hD
    simp [hD]
  calc
    E.filter (fun D => decide (x ∈ D ∧ D ∉ E.take k)) =
        (E.take k ++ E.drop k).filter (fun D => decide (x ∈ D ∧ D ∉ E.take k)) :=
      congrArg (List.filter (fun D => decide (x ∈ D ∧ D ∉ E.take k))) hSplit
    _ = _ := by rw [List.filter_append, hOld, List.nil_append]

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- At the empty lower history of the literal positive selected record,
the order companion counts precisely the incident born slots that survived
the member restriction. The count is independent of the order parameter. -/
theorem restarted_positive_companion_level_eq_born_count {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (H : BlowupTower X Y) (s o : ℕ) (x : Y)
    (hx : x ∈ maskA M H x) :
    let O := maskA M H x
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := lowerMarkedM M (s + 1) H x
    let R := BlowupTower.refl (X := A)
    let W := ordMask (M := A) L o
    let J := compAt (X := A) L o R
    ∀ h : (⟨x, hx⟩ : O) ∈ W,
      level J (BlowupTower.refl (X := CMfd.of (n := n) W)) (⟨⟨x, hx⟩, h⟩ : W) =
        (((geoTransformAlong (barMarked M) H).E.drop M.E.length).filter
          fun D => decide (x ∈ D ∧ D ∉ origMembers M H)).length := by
  intro O A L R W J h
  let B := geoTransformAlong (barMarked M) H
  let K := memberRestrict B (membersThrough B.E (origMembers M H) x)
  have hJ : J.E = L.E.map ((Subtype.val : W → O) ⁻¹' ·) := by
    change (companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → O) L) o).E = _
    exact companionAlong_E _ _ _ _ _ _
  have hL : L.E = K.E.map ((Subtype.val : O → Y) ⁻¹' ·) := rfl
  change boundaryCount (J.E.take J.E.length) (⟨⟨x, hx⟩, h⟩ : W) = _
  rw [List.take_length, hJ, CodimOnePartCanonical.boundaryCount_map_preimage, hL,
    CodimOnePartCanonical.boundaryCount_map_preimage, memberRestrict_membersThrough_E,
    boundaryCount_eq_countP, List.countP_eq_length_filter]
  exact congrArg List.length (selected_incident_slots B.E M.E.length x)

set_option backward.isDefEq.respectTransparency false in
/-- A positive inner level at a restarted order companion requires an
incident exceptional member from the actual history before that restart. -/
theorem restarted_positive_inner_level_requires_birth {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (H : BlowupTower X Y) (s o : ℕ) (x : Y)
    (hx : x ∈ maskA M H x) :
    let O := maskA M H x
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := lowerMarkedM M (s + 1) H x
    let W := ordMask (M := A) L o
    let J := compAt (X := A) L o (.refl (X := A))
    ∀ h : (⟨x, hx⟩ : O) ∈ W,
      0 < level J (BlowupTower.refl (X := CMfd.of (n := n) W)) (⟨⟨x, hx⟩, h⟩ : W) →
        ∃ D ∈ (geoTransformAlong (barMarked M) H).E.drop M.E.length,
          x ∈ D ∧ D ∉ origMembers M H := by
  intro O A L W J h hp
  rw [restarted_positive_companion_level_eq_born_count M H s o x hx h] at hp
  classical
  obtain ⟨D, hD⟩ := List.length_pos_iff_exists_mem.mp hp
  exact ⟨D, (List.mem_filter.mp hD).1, of_decide_eq_true (List.mem_filter.mp hD).2⟩


set_option backward.isDefEq.respectTransparency false in
/-- Under closed original boundary, a positive inner restart lies on the
support of the actual composite exceptional divisor of that recursive history. -/
theorem restarted_positive_inner_level_mem_exceptional_support {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (H : BlowupTower X Y) (s o : ℕ) (x : Y)
    (hClosed : ∀ D ∈ M.E, IsClosed D) (hx : x ∈ maskA M H x) :
    let O := maskA M H x
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := lowerMarkedM M (s + 1) H x
    let W := ordMask (M := A) L o
    let J := compAt (X := A) L o (.refl (X := A))
    ∀ h : (⟨x, hx⟩ : O) ∈ W,
      0 < level J (BlowupTower.refl (X := CMfd.of (n := n) W)) (⟨⟨x, hx⟩, h⟩ : W) →
        x ∈ (exceptionalDivisor H).support := by
  intro O A L W J h hp
  obtain ⟨D, hD, hxD, _⟩ := restarted_positive_inner_level_requires_birth M H s o x hx h hp
  have he : (barMarked M).E.length = M.E.length := rfl
  rw [support_exceptionalDivisor_eq_biUnion_drop (barMarked M) hClosed H, he]
  exact mem_iUnion.mpr ⟨D, mem_iUnion.mpr ⟨hD, hxD⟩⟩

private theorem born_slots_empty_of_isEmptyTower {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) : ∀ {Y : CMfd.{0} n} (H : BlowupTower X Y), IsEmptyTower H →
    ∀ D ∈ (geoTransformAlong M H).E.drop M.E.length, D = ∅
  | _, .refl, _, _, hD => by rw [geoTransformAlong_refl, List.drop_length] at hD; exact (List.not_mem_nil hD).elim
  | _, .step T C π hπ, h, D, hD => by
    obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := h
    have hLen : M.E.length ≤ ((geoTransformAlong M T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, length_E_geoTransformAlong]
      omega
    rw [geoTransformAlong_step, geoTransform_E, List.drop_append_of_le_length hLen, ← List.map_drop] at hD
    rcases List.mem_append.mp hD with hD | hD
    · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.mp hD
      rw [born_slots_empty_of_isEmptyTower M T hT D₀ hD₀]
      exact geoStrictTransform_eq_empty_of_subset (empty_subset C)
    · rw [List.mem_singleton] at hD
      rw [hD, hC, preimage_empty]

set_option backward.isDefEq.respectTransparency false in
/-- Empty centres do not create incident exceptional members. In
particular, a positive selection at an empty recursive tail has inner
companion level zero, regardless of the currently retained boundary. -/
theorem restarted_positive_companion_level_zero_of_isEmptyTower {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (H : BlowupTower X Y) (hH : IsEmptyTower H)
    (s o : ℕ) (x : Y) (hx : x ∈ maskA M H x) :
    let O := maskA M H x
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := lowerMarkedM M (s + 1) H x
    let W := ordMask (M := A) L o
    let J := compAt (X := A) L o (.refl (X := A))
    ∀ h : (⟨x, hx⟩ : O) ∈ W,
      level J (BlowupTower.refl (X := CMfd.of (n := n) W)) (⟨⟨x, hx⟩, h⟩ : W) = 0 := by
  intro O A L W J h
  by_contra hne
  obtain ⟨D, hD, hxD, _⟩ := restarted_positive_inner_level_requires_birth M H s o x hx h
    (Nat.pos_of_ne_zero hne)
  have he : (barMarked M).E.length = M.E.length := rfl
  rw [← he] at hD
  rw [born_slots_empty_of_isEmptyTower (barMarked M) H hH D hD] at hxD
  exact hxD

set_option backward.isDefEq.respectTransparency false in
/-- The obstruction also applies to the actual recursive read, including
its genuine domain and canonicality requirements. At a positive selected
cut with an empty-centre history, a positive true order reads a companion
whose Step One first coordinate is zero. -/
theorem actual_positive_successor_read_inner_zero_of_isEmptyTower
    {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (H : BlowupTower X Y) (hH : IsEmptyTower H)
    (s o : ℕ) (x : Y) (hx : x ∈ maskA M H x) (ho : 0 < o) :
    let O := maskA M H x
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := lowerMarkedM M (s + 1) H x
    let R := BlowupTower.refl (X := A)
    let z : O := ⟨x, hx⟩
    IsInvDomain (k + 1) L → z ∈ L.cosupp → nmOrd (M := A) L z = o →
      ∃ v : ℕ ×ₗ WithTop (ValTy k),
        (ofLex v).1 = 0 ∧ (invFamily hn (k + 1)).inv L R z = positiveSuccessorRead o v := by
  intro O A L R z hL hz hOrd
  have he := original_positive_order_successor_read (k := k) hn (X := A) L hL R trivial z hz o hOrd ho
  obtain ⟨hf, _, _, _, _, hVal⟩ := he
  let W := ordMask (M := A) L o
  let J := compAt (X := A) L o R
  let B := CMfd.of (n := n) W
  let p : W := ⟨z, hf⟩
  let T := BlowupTower.refl (X := B)
  let v := Seq.StepOneValueMasked.stepOneInvM (X := B) (invFamily hn k) J T p
  have hLevel : level J T p = 0 :=
    restarted_positive_companion_level_zero_of_isEmptyTower M H hH s o x hx hf
  have hv : (ofLex v).1 = 0 := by
    change (ofLex (Seq.StepOneValueMasked.stepOneInvL (X := B) (invFamily hn k) J
      (lowerMarkedM J) T p)).1 = 0
    rw [Seq.StepOneValueMasked.stepOneInvL_fst]
    exact hLevel
  exact ⟨v, hv, hVal⟩

set_option backward.isDefEq.respectTransparency false in
/-- On a positive selected cut reached using only empty centres, no
positive-inner-level letter at the true order can give the actual value. -/
theorem actual_positive_successor_read_ne_positive_inner_of_isEmptyTower
    {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (H : BlowupTower X Y) (hH : IsEmptyTower H)
    (s o : ℕ) (x : Y) (hx : x ∈ maskA M H x) (ho : 0 < o) :
    let O := maskA M H x
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := lowerMarkedM M (s + 1) H x
    let R := BlowupTower.refl (X := A)
    let z : O := ⟨x, hx⟩
    IsInvDomain (k + 1) L → z ∈ L.cosupp → nmOrd (M := A) L z = o →
      ∀ w : ℕ ×ₗ WithTop (ValTy k), 0 < (ofLex w).1 →
        (invFamily hn (k + 1)).inv L R z ≠ positiveSuccessorRead o w := by
  intro O A L R z hL hz hOrd w hw he
  obtain ⟨v, hv, hVal⟩ := actual_positive_successor_read_inner_zero_of_isEmptyTower
    (k := k) hn M H hH s o x hx ho hL hz hOrd
  have hRead := congrArg (fun t : ValTy (k + 1) => ofLex (ofLex t).2) (hVal.symm.trans he)
  change Sum.inr (↑v : WithTop (ℕ ×ₗ WithTop (ValTy k))) =
    Sum.inr (↑w : WithTop (ℕ ×ₗ WithTop (ValTy k))) at hRead
  have hCoord := congrArg (fun a : ℕ ×ₗ WithTop (ValTy k) => (ofLex a).1)
    (WithTop.coe_injective (Sum.inr.inj hRead))
  exact (Nat.ne_of_gt hw) (hCoord.symm.trans hv)

end
end Hironaka.HironakaG1NestedPositiveBirthObstruction
