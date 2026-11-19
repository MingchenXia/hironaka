import Hironaka.Resolution.HironakaG8FiniteSpatialRealization

/-! An injective rank respecting intersecting centre footprints can be
read as a finite physical TEST chart in increasing rank order. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8RankSortedSpatialChart

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8OccupiedSlotComparison HironakaG8FiniteSpatialRealization

private theorem sorted_rank_order {κ : Type*} [LinearOrder κ] (N : ℕ) (rank : ℕ → κ)
    (hInjective : InjOn rank {i | i < N}) :
    ∃ target : List ℕ, (List.range N).Perm target ∧ target.Pairwise (fun i j => rank i < rank j) := by
  let leRank (a b : ℕ) : Bool := decide (rank a ≤ rank b)
  let target := (List.range N).mergeSort leRank
  have hPerm : (List.range N).Perm target := (List.mergeSort_perm _ _).symm
  have hTrans : ∀ a b c, leRank a b → leRank b c → leRank a c := by
    intro a b c hab hbc
    exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have hTotal : ∀ a b, leRank a b || leRank b a := by
    intro a b
    simpa [leRank] using le_total (rank a) (rank b)
  have hSorted : target.Pairwise (fun a b => rank a ≤ rank b) := by
    simpa [leRank, target] using List.pairwise_mergeSort hTrans hTotal (List.range N)
  have hNodup : target.Nodup := hPerm.nodup_iff.mp List.nodup_range
  refine ⟨target,hPerm, List.Pairwise.imp_of_mem ?_ (hSorted.and hNodup)⟩
  intro a b ha hb h
  have haN := List.mem_range.mp (hPerm.mem_iff.mpr ha)
  have hbN := List.mem_range.mp (hPerm.mem_iff.mpr hb)
  exact lt_of_le_of_ne h.1 (fun he => h.2 (hInjective haN hbN he))

private theorem idxOf_lt_of_sorted_rank {κ : Type*} [LinearOrder κ]
    {target : List ℕ} {rank : ℕ → κ}
    (hTarget : target.Pairwise (fun i j => rank i < rank j))
    {i j : ℕ} (hi : i ∈ target) (hj : j ∈ target) (hRank : rank i < rank j) :
    target.idxOf i < target.idxOf j := by
  have hiLen := List.idxOf_lt_length_iff.mpr hi
  have hjLen := List.idxOf_lt_length_iff.mpr hj
  have hReadI : target[target.idxOf i] = i := List.getElem_idxOf hiLen
  have hReadJ : target[target.idxOf j] = j := List.getElem_idxOf hjLen
  rcases lt_trichotomy (target.idxOf i) (target.idxOf j) with hlt | heq | hgt
  · exact hlt
  · have hSome := List.getElem?_idxOf hi
    rw [heq,List.getElem?_idxOf hj] at hSome
    exact ((ne_of_lt hRank) (congrArg rank (Option.some.inj hSome).symm)).elim
  · have hReverse := (List.pairwise_iff_getElem.mp hTarget) _ _ hjLen hiLen hgt
    rw [hReadJ,hReadI] at hReverse
    exact (lt_asymm hReverse hRank).elim

/-- The rank-sorted index list and its order-preservation rule on the
original finite range, before choosing any physical realization. -/
theorem exists_key_sorted_spatial_target {κ : Type*} [LinearOrder κ] (N : ℕ) (rank : ℕ → κ)
    (hInjective : InjOn rank {i | i < N}) :
    ∃ target : List ℕ, (List.range N).Perm target ∧
      target.Pairwise (fun i j => rank i < rank j) ∧
      ∀ i j, i < j → j < N → rank i < rank j → target.idxOf i < target.idxOf j := by
  obtain ⟨target,hPerm,hSorted⟩ := sorted_rank_order N rank hInjective
  refine ⟨target,hPerm,hSorted,?_⟩
  intro i j hij hj hRank
  exact idxOf_lt_of_sorted_rank hSorted
    (hPerm.mem_iff.mp (List.mem_range.mpr (hij.trans hj)))
    (hPerm.mem_iff.mp (List.mem_range.mpr hj)) hRank

/-- The natural-key specialization of finite spatial sorting. -/
theorem exists_sorted_spatial_target (N : ℕ) (rank : ℕ → ℕ)
    (hInjective : InjOn rank {i | i < N}) :
    ∃ target : List ℕ, (List.range N).Perm target ∧
      target.Pairwise (fun i j => rank i < rank j) ∧
      ∀ i j, i < j → j < N → rank i < rank j → target.idxOf i < target.idxOf j :=
  exists_key_sorted_spatial_target N rank hInjective

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Sort an all-occupied finite chart by a rank respecting the
chronological order of intersecting projected centres. The given rank
determines only the order of the realized occupied stages. -/
theorem exists_rank_sorted_singular_test_chart
    (T : BlowupTower X Y) (rank : ℕ → ℕ) (hInjective : InjOn rank {i | i < T.length})
    (hOcc : ∀ i < T.length, (slotFootprint T i).Nonempty)
    (hRank : ∀ i j, i < j → j < T.length →
      (slotFootprint T i ∩ slotFootprint T j).Nonempty → rank i < rank j)
    (W : Set X) (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ target : List ℕ, (List.range T.length).Perm target ∧
      target.Pairwise (fun i j => rank i < rank j) ∧
      ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
        (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z),
        IsGeoTestTower M Q ∧ Q.proj ∘ e = T.proj ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
        (∀ j a, target[j]? = some a → slotFootprint Q j = slotFootprint T a) ∧
        ∀ j, (slotFootprint Q j).Nonempty ↔ j < target.length := by
  obtain ⟨target,hPerm,hTarget,hOrder⟩ := exists_sorted_spatial_target T.length rank hInjective
  refine ⟨target,hPerm,hTarget, realize_target_intersection_order T target hPerm hOcc ?_ W M hM hN hTest hStage⟩
  intro i j hij hj hMeet
  exact hOrder i j hij hj (hRank i j hij hj hMeet)

end Hironaka.HironakaG8RankSortedSpatialChart
