import Hironaka.Resolution.HironakaG8SortedRankExactPacking
import Hironaka.Resolution.HironakaG8PackedSingularStages

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8PackedRoundChart

open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder HironakaG8NestedVisibleWordLift
  HironakaG8FinitePartitionPacking HironakaG8SortedRankExactPacking HironakaG8PackedSingularStages

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- The weak rank of the literal raw position, with an irrelevant fallback
outside the exact source range of the order list. -/
def orderRank {α : Type*} (order : List α) (rank : α → ℕ) (j : ℕ) : ℕ :=
  (order[j]?.map rank).getD 0

/-- The packed chart has the actual original terminal object and projection,
one nonempty centre per occurring round, and an exact indexed dictionary. -/
theorem pack_round_chart {α : Type*}
    (T : BlowupTower X Y) (order : List α) (rank : α → ℕ) (roundFoot : ℕ → Set X)
    (hLen : T.length = order.length)
    (hOccupied : ∀ j, (slotFootprint T j).Nonempty ↔ j < order.length)
    (hSorted : order.Pairwise (fun p q => rank p ≤ rank q))
    (hDisj : ∀ i j p q, i ≠ j → order[i]? = some p → order[j]? = some q →
      rank p = rank q → Disjoint (slotFootprint T i) (slotFootprint T j))
    (hRound : ∀ r, rankFootprint T (orderRank order rank) r = roundFoot r)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hTest : IsGeoTestTower M T)
    (W : Set X) (hSing : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj W)) T)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W)) :
    ∃ (G : BlowupTower X Y) (labels : List ℕ),
      BlockPacking X T G (labels.map roundFoot) ∧ labels.Pairwise (· < ·) ∧
      (∀ r, r ∈ labels ↔ (roundFoot r).Nonempty) ∧
      G.length = labels.length ∧
      (∀ j r, labels[j]? = some r → slotFootprint G j = roundFoot r) ∧
      (∀ j, (slotFootprint G j).Nonempty ↔ j < labels.length) ∧
      G.proj = T.proj ∧ IsGeoTestTower M G ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) G ∧
      IsClosedSubmanifold n (strictTransform n G.proj W) := by
  let r := orderRank order rank
  have hRead j (hj : j < order.length) : r j = rank order[j] := by
    simp [r,orderRank,List.getElem?_eq_getElem hj]
  have hMono i j (hij : i ≤ j) (hj : j < T.length) : r i ≤ r j := by
    rcases lt_or_eq_of_le hij with h | rfl
    · have hj' := hLen ▸ hj
      rw [hRead i (h.trans hj'),hRead j hj']
      exact List.pairwise_iff_getElem.mp hSorted i j (h.trans hj') hj' h
    · exact le_rfl
  have hEqualDisj i j (hij : i < j) (hj : j < T.length) (hEq : r i = r j) :
      Disjoint (slotFootprint T i) (slotFootprint T j) := by
    have hj' := hLen ▸ hj
    have hi' := hij.trans hj'
    exact hDisj i j _ _ (ne_of_lt hij) (List.getElem?_eq_getElem hi')
      (List.getElem?_eq_getElem hj') ((hRead i hi').symm.trans (hEq.trans (hRead j hj')))
  obtain ⟨G,labels,hG,hLabels,hOccurs,hProj,hGTest⟩ :=
    pack_sorted_rank_test r T hMono hEqualDisj M hM hTest
  have hFn : rankFootprint T r = roundFoot := funext hRound
  have hTrace : BlockPacking X T G (labels.map roundFoot) := hFn ▸ hG
  have hFoot := hTrace.footprints_eq
  have hGLen : G.length = labels.length := by simpa [footprints] using congrArg List.length hFoot
  have hLabel (k : ℕ) : k ∈ labels ↔ (roundFoot k).Nonempty := by
    rw [hOccurs,← hRound]
    constructor
    · rintro ⟨j,hj,hr⟩
      obtain ⟨x,hx⟩ := (hOccupied j).mpr (hLen ▸ hj)
      exact ⟨x,mem_iUnion.mpr ⟨⟨j,hj,hr⟩,hx⟩⟩
    · rintro ⟨x,hx⟩
      obtain ⟨j,_⟩ := mem_iUnion.mp hx
      exact ⟨j.val,j.property⟩
  have hSlot j k (hk : labels[j]? = some k) : slotFootprint G j = roundFoot k := by
    obtain ⟨hj,_⟩ := List.getElem?_eq_some_iff.mp hk
    have hj' : j < G.length := hGLen.symm ▸ hj
    have hAt := congrArg (fun l : List (Set X) => l[j]?) hFoot
    simpa [footprints,hj',hk] using hAt
  refine ⟨G,labels,hTrace,hLabels,hLabel,hGLen,hSlot,?_,hProj,hGTest,
    blockPacking_intrinsic_stages hG W hSing,?_⟩
  · intro j
    constructor
    · rintro ⟨x,hx⟩
      exact hGLen ▸ hit_slot_lt_length G hx
    · intro hj
      rw [hSlot _ _ (List.getElem?_eq_getElem hj)]
      exact (hLabel _).mp (List.getElem_mem hj)
  · rw [hProj]
    exact hSmooth

end Hironaka.HironakaG8PackedRoundChart
