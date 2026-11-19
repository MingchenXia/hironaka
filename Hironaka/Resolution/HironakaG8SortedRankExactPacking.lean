import Hironaka.Resolution.HironakaG8FinitePartitionPacking
import Hironaka.Blowup.BlowupTowerSplit

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SortedRankExactPacking

open BlowupTowers BlowupTowerSplit HironakaG8FirstFootprintOrder
  HironakaG8OccupiedSlotComparison HironakaG8FinitePartitionPacking HironakaG8FiniteParallelGeometry
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8ParallelBlocksJoin BlowupTowerTransforms

variable {n : ℕ} {X : CMfd.{0} n}

/-- Group by the literal projected footprints at the specified original rank. -/
def rankFootprint {Y : CMfd.{0} n} {κ : Type*} (T : BlowupTower X Y)
    (rank : ℕ → κ) (r : κ) : Set X :=
  ⋃ j : {i // i < T.length ∧ rank i = r}, slotFootprint T j.val

/-- Perform one actual grouped blowup for every occupied rank of a sorted
finite tower, retaining the exact rank order and projected union dictionary. -/
theorem pack_sorted_rank_exact {κ : Type*} [LinearOrder κ] (rank : ℕ → κ)
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hMono : ∀ i j, i ≤ j → j < T.length → rank i ≤ rank j)
    (hRank : ∀ i j, i < j → j < T.length → rank i = rank j →
      Disjoint (slotFootprint T i) (slotFootprint T j)) :
    ∃ (G : BlowupTower X Y) (labels : List κ),
      BlockPacking X T G (labels.map (rankFootprint T rank)) ∧
        labels.Pairwise (· < ·) ∧
        ∀ r, r ∈ labels ↔ ∃ j < T.length, rank j = r := by
  classical
  generalize eq : T.length = N
  induction N using Nat.strong_induction_on generalizing Y with
  | h N ih =>
      by_cases hN : N = 0
      · cases T with
        | refl =>
          refine ⟨.refl,[],.nil,by simp,?_⟩
          simp [hN]
        | step P C π hπ => simp [hN] at eq
      have hEnd : ∃ k, k < N ∧ ∀ i, k ≤ i → i < N → rank i = rank (N-1) := by
        refine ⟨N-1,by omega,?_⟩
        intro i hi hj
        have he : i = N-1 := by omega
        rw [he]
      let k := Nat.find hEnd
      obtain ⟨hk,hRankTail⟩ := Nat.find_spec hEnd
      let P := head T (N-k)
      let S := tail T (N-k)
      have hPS : P.append S = T := head_append_tail T _
      have hPLen : P.length = k := by rw [length_head,eq]; omega
      have hSLen : S.length = N-k := by rw [length_tail,eq,min_eq_left (Nat.sub_le _ _)]
      have hSmall : P.length < N := by rw [hPLen]; exact hk
      let r := rank (N-1)
      have hBefore i (hi : i < P.length) : slotFootprint P i = slotFootprint T i :=
        (by rw [slotFootprint_append,if_pos hi] :
          slotFootprint (P.append S) i = slotFootprint P i).symm.trans
            (congrArg (fun R => slotFootprint R i) hPS)
      have hAfter i : P.proj '' slotFootprint S i = slotFootprint T (P.length+i) :=
        (by rw [slotFootprint_append,if_neg (by omega),Nat.add_sub_cancel_left] :
          slotFootprint (P.append S) (P.length+i) = P.proj '' slotFootprint S i).symm.trans
            (congrArg (fun R => slotFootprint R (P.length+i)) hPS)
      have hEarlier i (hi : i < P.length) : rank i < r := by
        have hLe : rank i ≤ r := hMono _ _ (by omega) (by omega)
        refine lt_of_le_of_ne hLe ?_
        intro he
        have hCut : i < N ∧ ∀ j, i ≤ j → j < N → rank j = rank (N-1) := by
          refine ⟨by omega,?_⟩
          intro j hij hj
          exact le_antisymm (hMono _ _ (by omega) (by omega))
            (by have hh := hMono i j hij (by omega); rw [he] at hh; exact hh)
        have hMin := Nat.find_min' hEnd hCut
        omega
      obtain ⟨GP,labels,hP,hSorted,hLabels⟩ := ih P.length hSmall P
        (fun i j hij hj => hMono i j hij (by omega))
        (fun i j hij hj he => by
          rw [hBefore i (hij.trans hj),hBefore j hj]
          exact hRank i j hij (by omega) he) rfl
      have hApart (i j : ℕ) (hij : i < j) (hj : j < S.length) :
          Disjoint (P.proj '' slotFootprint S i) (P.proj '' slotFootprint S j) := by
        rw [hAfter,hAfter]
        apply hRank _ _ (by omega) (by omega)
        exact (hRankTail _ (by omega) (by omega)).trans (hRankTail _ (by omega) (by omega)).symm
      have hDisj (i j : ℕ) (hij : i < j) (hj : j < S.length) :
          Disjoint (slotFootprint S i) (slotFootprint S j) := by
        rw [Set.disjoint_left]
        intro x hxi hxj
        exact Set.disjoint_left.mp (hApart i j hij hj)
          (mem_image_of_mem _ hxi) (mem_image_of_mem _ hxj)
      have hPrev (s : κ) (hs : s ∈ labels) : rankFootprint P rank s = rankFootprint T rank s := by
        obtain ⟨i,hi,hei⟩ := (hLabels s).mp hs
        have hsLt : s < r := hei ▸ hEarlier i hi
        ext x
        simp only [rankFootprint,mem_iUnion]
        constructor
        · rintro ⟨⟨j,hj,hjr⟩,hx⟩
          exact ⟨⟨j,by omega,hjr⟩,(hBefore j hj) ▸ hx⟩
        · rintro ⟨⟨j,hj,hjr⟩,hx⟩
          have hjP : j < P.length := by
            by_contra! hGe
            have heq := hRankTail j (by omega) (by omega)
            exact (ne_of_lt hsLt) (hjr.symm.trans heq)
          exact ⟨⟨j,hjP,hjr⟩,(hBefore j hjP).symm ▸ hx⟩
      have hLast : P.proj '' blockCentre S = rankFootprint T rank r := by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          obtain ⟨j,hj⟩ := mem_iUnion.mp hy
          have hjL := hit_slot_lt_length S hj
          exact mem_iUnion.mpr ⟨⟨P.length+j,by omega,hRankTail _ (by omega) (by omega)⟩,
            (hAfter j) ▸ mem_image_of_mem P.proj hj⟩
        · intro hx
          obtain ⟨⟨j,hj,hjr⟩,hx⟩ := mem_iUnion.mp hx
          have hjP : P.length ≤ j := by
            by_contra! hh
            exact (ne_of_lt (hEarlier j hh)) hjr
          have hjEq : P.length+(j-P.length) = j := by omega
          have hIndex := hAfter (j-P.length)
          rw [hjEq] at hIndex
          have hh : x ∈ P.proj '' slotFootprint S (j-P.length) := hIndex.symm ▸ hx
          obtain ⟨y,hy,he⟩ := hh
          exact ⟨y,mem_iUnion.mpr ⟨j-P.length,hy⟩,he⟩
      let hπ := isBlowupAlong_blockCentre_of_disjoint S hDisj
      let G := BlowupTower.step GP (blockCentre S) S.proj hπ
      have hMap : labels.map (rankFootprint P rank) = labels.map (rankFootprint T rank) :=
        List.map_congr_left hPrev
      have hPacking : BlockPacking X (P.append S) G
          (labels.map (rankFootprint P rank) ++ [P.proj '' blockCentre S]) :=
        .append hP S hApart hπ
      have hPacking' : BlockPacking X T G ((labels ++ [r]).map (rankFootprint T rank)) := by
        rw [List.map_append,List.map_singleton,← hLast,← hMap]
        exact (congrArg (fun T₀ => BlockPacking X T₀ G
          (labels.map (rankFootprint P rank) ++ [P.proj '' blockCentre S])) hPS).mp hPacking
      refine ⟨G,labels ++ [r],hPacking',?_,?_⟩
      · rw [List.pairwise_append]
        refine ⟨hSorted,by simp,?_⟩
        intro a ha b hb
        obtain ⟨i,hi,hei⟩ := (hLabels a).mp ha
        have hb' : b = r := by simpa using hb
        rw [← hei,hb']
        exact hEarlier i hi
      · intro s
        rw [List.mem_append,List.mem_singleton,hLabels]
        constructor
        · rintro (⟨j,hj,he⟩ | rfl)
          · exact ⟨j,by omega,he⟩
          · exact ⟨N-1,by omega,rfl⟩
        · rintro ⟨j,hj,hjr⟩
          by_cases hJP : j < P.length
          · exact Or.inl ⟨j,hJP,hjr⟩
          · exact Or.inr (hjr.symm.trans (hRankTail j (by omega) (by omega)))


/-- The ranked packed tower retains the whole original TEST and exact
terminal projection. Its raw footprint list is the sorted rank-union list. -/
theorem pack_sorted_rank_test {κ : Type*} [LinearOrder κ] (rank : ℕ → κ)
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hMono : ∀ i j, i ≤ j → j < T.length → rank i ≤ rank j)
    (hRank : ∀ i j, i < j → j < T.length → rank i = rank j →
      Disjoint (slotFootprint T i) (slotFootprint T j))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hT : IsGeoTestTower M T) :
    ∃ (G : BlowupTower X Y) (labels : List κ),
      BlockPacking X T G (labels.map (rankFootprint T rank)) ∧
        labels.Pairwise (· < ·) ∧ (∀ r, r ∈ labels ↔ ∃ j < T.length, rank j = r) ∧
        G.proj = T.proj ∧ IsGeoTestTower M G := by
  classical
  obtain ⟨G,labels,hG,hSorted,hLabels⟩ := pack_sorted_rank_exact rank T hMono hRank
  have hLoc (x : X) := hG.local_cover x ⊤ trivial
  choose U hU _ hData using hLoc
  refine ⟨G,labels,hG,hSorted,hLabels,hG.proj_eq,
    grouped_test_of_local_comparisons M hM T G hT U (fun x => ⟨x,hU x⟩) ?_⟩
  intro x
  obtain ⟨e,_,he⟩ := hData x
  exact ⟨e,he⟩

end Hironaka.HironakaG8SortedRankExactPacking
