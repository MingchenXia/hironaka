import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

/-! A weak spatial clock with bounded visible width in each epoch. -/
set_option autoImplicit false
open Set
open scoped BigOperators
namespace Hironaka.HironakaG8WeakSpatialRankByEpoch

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8OccupiedSlotComparison HironakaG8SpatialCofinalPrecedence

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)

/-- If the epoch labels increase chronologically, footprint nesting is
only required within an epoch. Uniform pointwise epoch width allows one
natural rank even when transitions across epochs have infinite branching. -/
theorem exists_weak_spatial_rank_of_epoch_width
    (epoch : ι → ℕ) (height : ℕ → ℕ)
    (hEpoch : ∀ ⦃a b⦄, SpatialBefore E a b → epoch a ≤ epoch b)
    (hNest : ∀ ⦃a b⦄, SpatialBefore E a b → epoch a = epoch b →
      cofinalEventFootprint E b ⊆ cofinalEventFootprint E a)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hWidth : ∀ (x : X) (j : ℕ), ∃ F : Finset ι, F.card ≤ height j ∧
      ∀ a, epoch a = j → x ∈ cofinalEventFootprint E a → a ∈ F) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  classical
  let R (a b : ι) := SpatialBefore E a b ∧ epoch a = epoch b
  let A (b : ι) := {a | Relation.TransGen R a b}
  have hTrans {a b : ι} (h : Relation.TransGen R a b) :
      epoch a = epoch b ∧ cofinalEventFootprint E b ⊆ cofinalEventFootprint E a := by
    induction h with
    | single h => exact ⟨h.2,hNest h.1 h.2⟩
    | tail _ h ih => exact ⟨ih.1.trans h.2,(hNest h.1 h.2).trans ih.2⟩
  have hBefore {a b : ι} (h : Relation.TransGen R a b) : E.Before a b := by
    induction h with
    | single h => exact spatialBefore_imp_before E h.1
    | tail _ h ih => exact E.before_trans ih (spatialBefore_imp_before E h.1)
  have hFin (b : ι) : (A b).Finite ∧ (A b).ncard ≤ height (epoch b) := by
    obtain ⟨i,p,hp⟩ := hOccurs b
    obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c i).T p.val).mpr p.property
    have hb : x.val ∈ cofinalEventFootprint E b := ⟨i,p,hp,mem_image_of_mem _ hx⟩
    obtain ⟨F,hF,hContains⟩ := hWidth x.val (epoch b)
    have hSub : A b ⊆ (F : Set ι) := fun a ha =>
      hContains a (hTrans ha).1 ((hTrans ha).2 hb)
    exact ⟨F.finite_toSet.subset hSub,
      (Set.ncard_le_ncard hSub F.finite_toSet).trans (by simpa using hF)⟩
  let base (j : ℕ) := ∑ k ∈ Finset.range j, (height k + 1)
  have hBaseStep (j : ℕ) : base (j+1) = base j + (height j + 1) := Finset.sum_range_succ _ j
  have hBaseMono : Monotone base :=
    monotone_nat_of_le_succ fun j => by rw [hBaseStep]; omega
  refine ⟨fun b => base (epoch b) + (A b).ncard,?_⟩
  intro a b hab
  change base (epoch a) + (A a).ncard < base (epoch b) + (A b).ncard
  rcases lt_or_eq_of_le (hEpoch hab) with hlt | heq
  · have hBase := hBaseMono (Nat.succ_le_of_lt hlt)
    rw [hBaseStep] at hBase
    have hA := (hFin a).2
    omega
  · have hSub : A a ⊆ A b := fun _ h => .tail h ⟨hab,heq⟩
    have hStrict : A a ⊂ A b :=
      ⟨hSub,fun h => E.before_irrefl a (hBefore (h (.single ⟨hab,heq⟩)))⟩
    have hLen := Set.ncard_lt_ncard hStrict (hFin b).1
    rw [heq]
    omega


/-- A bound on the literal occupied raw slots of one containing chart
per point certifies the ambient pointwise width assumption. -/
theorem exists_weak_spatial_rank_of_chart_epoch_width
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (epoch : ι → ℕ) (height : ℕ → ℕ)
    (hEpoch : ∀ ⦃a b⦄, SpatialBefore E a b → epoch a ≤ epoch b)
    (hNest : ∀ ⦃a b⦄, SpatialBefore E a b → epoch a = epoch b →
      cofinalEventFootprint E b ⊆ cofinalEventFootprint E a)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hWidth : ∀ (x : X) (j : ℕ), ∃ (i : ℕ) (hx : x ∈ (c i).U)
      (F : Finset {k // Occupied (c i).T k}), F.card ≤ height j ∧
        ∀ p : {k // Occupied (c i).T k}, epoch (E.event i p) = j →
        (⟨x,hx⟩ : (c i).U) ∈ slotFootprint (c i).T p.val → p ∈ F) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b := by
  classical
  apply exists_weak_spatial_rank_of_epoch_width E epoch height hEpoch hNest hOccurs
  intro x j
  obtain ⟨i,hx,F,hF,hContains⟩ := hWidth x j
  refine ⟨F.image (E.event i),Finset.card_image_le.trans hF,?_⟩
  intro a hEpochA ha
  obtain ⟨p,hp,hFoot⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a hx).mp ha
  obtain ⟨y,hy,hyx⟩ := hFoot
  have hy' : y = (⟨x,hx⟩ : (c i).U) := Subtype.ext hyx
  exact Finset.mem_image.mpr ⟨p,hContains p (hp.symm ▸ hEpochA) (hy' ▸ hy),hp⟩

/-- Distinct events at one weak rank have disjoint whole cofinal
footprints, even when their original occurrences are on different charts. -/
theorem disjoint_cofinalEventFootprints_of_weak_rank_eq
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (rank : ι → ℕ) (hRank : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b)
    {a b : ι} (hNe : a ≠ b) (hEq : rank a = rank b) :
    Disjoint (cofinalEventFootprint E a) (cofinalEventFootprint E b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases E.before_total_of_occurs hOccurs hNe with hab | hba
  · have hs := (spatialBefore_iff_before_and_footprint_meets E cmp hMono hLift).mpr
      ⟨hab,x,hx,hy⟩
    exact (Nat.ne_of_lt (hRank hs)) hEq
  · have hs := (spatialBefore_iff_before_and_footprint_meets E cmp hMono hLift).mpr
      ⟨hba,x,hy,hx⟩
    exact (Nat.ne_of_lt (hRank hs)) hEq.symm

end Hironaka.HironakaG8WeakSpatialRankByEpoch
