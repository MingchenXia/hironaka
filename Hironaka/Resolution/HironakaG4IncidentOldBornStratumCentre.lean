import Hironaka.Invariant.MemberInterAlong
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

set_option autoImplicit false

/-! Actual current born-NC centres with incident-only old germ containment have
full old++born NC; real born strata supply the current born geometry internally.
Complete source-first chapter: hironaka-g4-incident-old-born-stratum-centre.tex. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4IncidentOldBornStratumCentre

noncomputable section

open Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  BoundaryCount MemberInterAlong HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalAllBoundaryCentre

variable {n : ℕ} {X : CMfd.{u} n}

private theorem exists_contained_or_absent_old_window {C : Set X} {old : List (Set X)}
    (hClosed : ∀ i : Fin old.length, IsClosed (old.get i)) {x : X}
    (hlocal : ∀ i : Fin old.length, x ∈ old.get i →
      ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ old.get i) :
    ∃ U : Opens X, x ∈ U ∧ ∀ i : Fin old.length,
      (Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' old.get i ∨
        ((Subtype.val : U → X) ⁻¹' old.get i : Set U) = ∅ := by
  have hNear : ∀ᶠ y in 𝓝 x, ∀ i : Fin old.length,
      if x ∈ old.get i then (y ∈ C → y ∈ old.get i) else y ∉ old.get i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x ∈ old.get i
    · simpa only [if_pos hi] using hlocal i hi
    · have hEvent : ∀ᶠ y in 𝓝 x, y ∉ old.get i := (hClosed i).isOpen_compl.mem_nhds hi
      simpa only [if_neg hi] using hEvent
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hNear
  let U : Opens X := ⟨V, hVo⟩
  refine ⟨U, hxV, ?_⟩
  intro i
  by_cases hi : x ∈ old.get i
  · left
    intro y hy
    have hContains : (y : X) ∈ C → (y : X) ∈ old.get i := by
      simpa only [if_pos hi] using hV y.property i
    exact hContains hy
  · right
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    have hAbsent : (y : X) ∉ old.get i := by
      simpa only [if_neg hi] using hV y.property i
    exact hAbsent hy

/-- Genuine CURRENT born-only NC and INCIDENT old germ containment produce
literal full centre NC, retaining every position; no future NC certificate. -/
theorem actual_incident_old_normalCrossingsAt
    {C : Set X} {old born : List (Set X)}
    (hE : IsSNCDivisor n (old ++ born)) (hCB : HasNormalCrossings n C born)
    {x : X} (hx : x ∈ C)
    (hlocal : ∀ i : Fin old.length, x ∈ old.get i →
      ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ old.get i) :
    normalCrossingsAt (n := n) C (old ++ born) x := by
  obtain ⟨U, hxU, hCases⟩ := exists_contained_or_absent_old_window
    (fun i => hE.1 _ (List.mem_append_left born (List.get_mem old i))) hlocal
  let z : U := ⟨x, hxU⟩
  let CU : Set U := (Subtype.val : U → X) ⁻¹' C
  let EU := (old ++ born).map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hCBU : HasNormalCrossings n CU BU :=
    hasNormalCrossings_preimage (pullsBackCoordinates_val (n := n) U) hCB
  have hz : z ∈ CU := hx
  let I₀ : Finset (Fin EU.length) := Finset.univ.filter fun i => EU.get i ∈ BU
  let J : Finset (Fin EU.length) :=
    Finset.univ.filter fun i => z ∈ EU.get i ∧ EU.get i ∉ BU
  have hBase : IsPartialNCAt n CU EU I₀ z := isPartialNCAt_of_hasNormalCrossings hCBU hz
  have hContains : ∀ i ∈ J, CU ⊆ EU.get i := by
    intro i hi
    have hiJ := (Finset.mem_filter.mp hi).2
    obtain ⟨A, hA, hEA⟩ := List.mem_map.mp (List.get_mem EU i)
    have hOld : A ∈ old := by
      rcases List.mem_append.mp hA with hOld | hBorn
      · exact hOld
      · exact (hiJ.2 (List.mem_map.mpr ⟨A, hBorn, hEA⟩)).elim
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hOld
    have hEq : ((Subtype.val : U → X) ⁻¹' old.get k : Set U) = EU.get i := by
      rw [hk]
      exact hEA
    rcases hCases k with hContained | hEmpty
    · rw [← hEq]
      exact hContained
    · have hzOld : z ∈ (Subtype.val : U → X) ⁻¹' old.get k := by
        rw [hEq]
        exact hiJ.1
      rw [hEmpty] at hzOld
      exact hzOld.elim
  have hInsert : ∀ K : Finset (Fin EU.length), (∀ i ∈ K, CU ⊆ EU.get i) →
      IsPartialNCAt n CU EU (I₀ ∪ K) z := by
    intro K
    refine Finset.induction_on K ?_ ?_
    · intro _
      simpa only [Finset.union_empty] using hBase
    · intro i K _ ih hK
      rw [Finset.union_insert]
      exact (ih fun j hj => hK j (Finset.mem_insert_of_mem hj)).insert hEU hz
        (hK i (Finset.mem_insert_self i K))
  have hAll := hInsert J hContains
  have hIncident : IsPartialNCAt n CU EU (Finset.univ.filter fun i => z ∈ EU.get i) z := by
    obtain ⟨Y, s, Θ, ht, h0, hC, hMembers⟩ := hAll
    refine ⟨Y, s, Θ, ht, h0, hC, ?_⟩
    intro i _hi hzi
    apply hMembers i ?_ hzi
    by_cases hiB : EU.get i ∈ BU
    · exact Finset.mem_union_left J (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiB⟩)
    · exact Finset.mem_union_right I₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hzi, hiB⟩)
  exact normalCrossingsAt_preimage_val_iff.mp
    (normalCrossingsAt_of_partial_incident (X := CMfd.of (n := n) U) hIncident)

/-- Genuine closed smooth full-boundary centre geometry from actual born
strata and incident-old germ containment, without caller centre NC. -/
theorem actual_incident_old_born_stratum_centre (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hT : IsTransverse n N born)
    (S : Finset (Fin born.length))
    (hlocal : ∀ x ∈ N ∩ memberInter born S, ∀ i : Fin old.length, x ∈ old.get i →
      ∀ᶠ y in 𝓝 x, y ∈ N ∩ memberInter born S → y ∈ old.get i) :
    IsClosedSubmanifold n (N ∩ memberInter born S) ∧
      HasNormalCrossings n (N ∩ memberInter born S) (old ++ born) := by
  refine ⟨isClosedSubmanifold_inter_memberInter hn hN.1
    (isSNCDivisor_of_sublist hE (List.sublist_append_right old born)) hT S, ?_⟩
  intro x hx
  exact actual_incident_old_normalCrossingsAt hE
    (hasNormalCrossings_inter_memberInter hT S) hx (hlocal x hx)

end
end Hironaka.HironakaG4IncidentOldBornStratumCentre
