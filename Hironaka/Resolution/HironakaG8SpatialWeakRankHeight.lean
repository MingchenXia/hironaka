import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

/-! Exact bounded-height criterion and a locally finite, infinitely branching footprint model. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG8SpatialWeakRankHeight

open BlowupTowers HironakaG3RTowerClass
  HironakaG8CofinalOccupiedAncestry HironakaG8SpatialCofinalPrecedence HironakaG8StageRankCoherence

theorem exists_weak_spatial_rank_iff_bounded_height
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι) :
    (∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b) ↔
      ∀ b, ∃ bound, ∀ l, DependencyPath (SpatialBefore E) l b → l ≤ bound :=
  exists_natural_rank_iff (SpatialBefore E)

/-- A noncompact common footprint intersects infinitely many individually
closed point footprints. The point footprints are pairwise disjoint. -/
def starFootprint : Option ℕ → Set ℕ
  | none => univ
  | some k => {k}

theorem locallyFinite_starFootprint : LocallyFinite starFootprint := by
  intro x
  have hOpen : IsOpen ({x} : Set ℕ) := isOpen_discrete _
  refine ⟨{x},hOpen.mem_nhds (mem_singleton x),((finite_singleton (some x)).insert none).subset ?_⟩
  intro a ha
  cases a with
  | none => exact mem_insert _ _
  | some k =>
    obtain ⟨y,hy,hx⟩ := ha
    have hyk : y = k := hy
    have hyx : y = x := hx
    exact mem_insert_of_mem _ (congrArg some (hyk.symm.trans hyx))

/-- Put the point events before the common event and orient their
intersections by that chronological order. -/
def starBefore (a b : Option ℕ) : Prop :=
  (a.isSome ∧ b = none) ∧ (starFootprint a ∩ starFootprint b).Nonempty

theorem starBefore_iff {a b : Option ℕ} :
    starBefore a b ↔ a.isSome ∧ b = none := by
  refine ⟨And.left,?_⟩
  rintro ⟨ha,rfl⟩
  cases a with
  | none => contradiction
  | some k => exact ⟨⟨ha,rfl⟩,k,mem_singleton k,mem_univ k⟩

/-- Infinite incoming branching is compatible with uniformly bounded
path length, since every leaf can share weak rank zero. -/
theorem star_weak_rank_and_infinite_incoming :
    (∃ rank : Option ℕ → ℕ, ∀ ⦃a b⦄, starBefore a b → rank a < rank b) ∧
      Set.Infinite {a | starBefore a none} ∧
      ∀ b l, DependencyPath starBefore l b → l ≤ 1 := by
  let rank : Option ℕ → ℕ := fun a => if a.isSome then 0 else 1
  have hr {a b : Option ℕ} (h : starBefore a b) : rank a < rank b := by
    obtain ⟨ha,rfl⟩ := starBefore_iff.mp h
    simp [rank,ha]
  refine ⟨⟨rank,fun {_ _} h => hr h⟩,?_,?_⟩
  · apply (Set.infinite_range_of_injective (Option.some_injective ℕ)).mono
    rintro a ⟨k,rfl⟩
    exact starBefore_iff.mpr ⟨rfl,rfl⟩
  · intro b l h
    have hBound : l ≤ rank b := by
      induction h with
      | nil => exact Nat.zero_le _
      | step h _ ih => exact Nat.succ_le_of_lt (ih.trans_lt (hr h))
    exact hBound.trans (by dsimp [rank]; split <;> omega)

theorem no_injective_star_rank :
    ¬ ∃ rank : Option ℕ → ℕ, Function.Injective rank ∧
      ∀ ⦃a b⦄, starBefore a b → rank a < rank b := by
  rintro ⟨rank,hInj,hRank⟩
  have hFinite : {a | starBefore a none}.Finite :=
    ((Set.finite_Iio (rank none)).preimage hInj.injOn).subset fun _ ha => hRank ha
  exact star_weak_rank_and_infinite_incoming.2.1 hFinite

end Hironaka.HironakaG8SpatialWeakRankHeight
