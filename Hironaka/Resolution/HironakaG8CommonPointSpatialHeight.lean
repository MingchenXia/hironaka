import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

/-! Pointwise geometric witnesses for bounded spatial ancestry. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG8CommonPointSpatialHeight

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts HironakaG8OccupiedSlotComparison
  HironakaG8SpatialCofinalPrecedence HironakaG8StageRankCoherence

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)

/-- Every edge is seen through the same original base point. -/
def SpatialBeforeAt (x : X) (a b : ι) : Prop :=
  SpatialBefore E a b ∧ x ∈ cofinalEventFootprint E a ∧ x ∈ cofinalEventFootprint E b

/-- A path through one point is bounded by the number of events visible
at that point in any containing actual chart. -/
theorem path_length_le_visible_events
    (x : X) (F : Finset ι) (hSeen : ∀ a, x ∈ cofinalEventFootprint E a → a ∈ F)
    {b : ι} {l : ℕ} (hPath : DependencyPath (SpatialBeforeAt E x) l b) : l ≤ F.card := by
  classical
  let lower (a : ι) := {b | b ∈ (F : Set ι) ∧ E.Before b a}
  have hFin (a : ι) : (lower a).Finite := F.finite_toSet.subset (fun _ h => h.1)
  have hLess {a b : ι} (h : SpatialBeforeAt E x a b) : (lower a).ncard < (lower b).ncard := by
    have hAB := spatialBefore_imp_before E h.1
    have hSub : lower a ⊆ lower b := fun _ h => ⟨h.1,E.before_trans h.2 hAB⟩
    have ha : a ∈ lower b := ⟨hSeen a h.2.1,hAB⟩
    apply Set.ncard_lt_ncard ⟨hSub,?_⟩ (hFin b)
    intro hBack
    exact E.before_irrefl a (hBack ha).2
  have hLen : l ≤ (lower b).ncard := by
    induction hPath with
    | nil => exact Nat.zero_le _
    | step h _ ih => exact Nat.succ_le_of_lt (ih.trans_lt (hLess h))
  have hSubF : lower b ⊆ (F : Set ι) := fun _ h => h.1
  exact hLen.trans (by simpa using Set.ncard_le_ncard hSubF F.finite_toSet)

/-- Common-point realizations of incoming paths give weak natural
rank if the width at a point is bounded along each terminal footprint.
The point may depend on the full path. -/
theorem exists_weak_spatial_rank_of_common_point_paths
    (hWitness : ∀ b l, DependencyPath (SpatialBefore E) l b →
      ∃ x ∈ cofinalEventFootprint E b, DependencyPath (SpatialBeforeAt E x) l b)
    (width : ι → ℕ)
    (hWidth : ∀ b x, x ∈ cofinalEventFootprint E b → ∃ F : Finset ι,
      F.card ≤ width b ∧ ∀ a, x ∈ cofinalEventFootprint E a → a ∈ F) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  apply (exists_natural_rank_iff (SpatialBefore E)).mpr
  intro b
  refine ⟨width b,fun l h => ?_⟩
  obtain ⟨x,hx,hPath⟩ := hWitness b l h
  obtain ⟨F,hF,hSeen⟩ := hWidth b x hx
  exact (path_length_le_visible_events E x F hSeen hPath).trans hF

/-- A genuine finite chart near each point of the final footprint
can certify the uniform width using only the literal raw slots through that point. -/
theorem exists_weak_spatial_rank_of_common_point_chart_width
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hWitness : ∀ b l, DependencyPath (SpatialBefore E) l b →
      ∃ x ∈ cofinalEventFootprint E b, DependencyPath (SpatialBeforeAt E x) l b)
    (width : ι → ℕ)
    (hWidth : ∀ b x, x ∈ cofinalEventFootprint E b → ∃ (i : ℕ) (hx : x ∈ (c i).U)
      (slots : Finset {k // Occupied (c i).T k}), slots.card ≤ width b ∧
        ∀ p : {k // Occupied (c i).T k}, (⟨x,hx⟩ : (c i).U) ∈ slotFootprint (c i).T p.val → p ∈ slots) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  classical
  apply exists_weak_spatial_rank_of_common_point_paths E hWitness width
  intro b x hx
  obtain ⟨i,hi,slots,hCap,hSlots⟩ := hWidth b x hx
  refine ⟨slots.image (E.event i),Finset.card_image_le.trans hCap,?_⟩
  intro a ha
  obtain ⟨p,hp,hTrace⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a hi).mp ha
  obtain ⟨y,hy,hyx⟩ := hTrace
  have hEq : y = (⟨x,hi⟩ : (c i).U) := Subtype.ext hyx
  exact Finset.mem_image.mpr ⟨p,hSlots p (hEq ▸ hy),hp⟩

/-- A compact test set for each terminal event supplies a uniform bound
when every incoming path length can be realized through a point of that set.
The compact set need only capture witnesses for lengths, and the terminal
footprint itself may be noncompact. -/
theorem exists_weak_spatial_rank_of_compact_path_witnesses
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (testSet : ι → Set X) (hCompact : ∀ b, IsCompact (testSet b))
    (hWitness : ∀ b l, DependencyPath (SpatialBefore E) l b →
      ∃ x ∈ testSet b, DependencyPath (SpatialBeforeAt E x) l b) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  classical
  have hLF := locallyFinite_cofinal_eventFootprints E cmp hMono hLift hCover
  apply (exists_natural_rank_iff (SpatialBefore E)).mpr
  intro b
  let hFinite := hLF.finite_nonempty_inter_compact (hCompact b)
  refine ⟨hFinite.toFinset.card,fun l hPath => ?_⟩
  obtain ⟨x,hx,hThrough⟩ := hWitness b l hPath
  exact path_length_le_visible_events E x hFinite.toFinset
    (fun _ ha => hFinite.mem_toFinset.mpr ⟨x,ha,hx⟩) hThrough

end Hironaka.HironakaG8CommonPointSpatialHeight
