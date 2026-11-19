import Hironaka.Resolution.HironakaG8PointCountRank
import Hironaka.Resolution.HironakaG8CommonPointSpatialHeight

/-! Read local predecessor counts through physical occupied slots and their comparisons. -/
set_option autoImplicit false
open Set

namespace Hironaka.HironakaG8CofinalLocalPointRank

open HironakaG8PointCountRank

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8OccupiedSlotComparison HironakaG8SpatialCofinalPrecedence

theorem cofinal_pointCount_eq_chart
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (E : CofinalEvents c I)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (i : ℕ) (x : (c i).U) (q : {k // Occupied (c i).T k}) :
    pointCount (cofinalEventFootprint E) E.Before x.val (E.event i q) =
      pointCount (fun p : {k // Occupied (c i).T k} => slotFootprint (c i).T p.val)
        (· < ·) x q := by
  apply Set.ncard_congr
    (fun a ha => Classical.choose
      ((mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a x.property).mp ha.1))
  · intro a ha
    let p := Classical.choose
      ((mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a x.property).mp ha.1)
    have hp := Classical.choose_spec
      ((mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a x.property).mp ha.1)
    refine ⟨?_,?_⟩
    · obtain ⟨y,hy,hyx⟩ := hp.2
      have he : y = x := Subtype.ext hyx
      exact he ▸ hy
    · change p.val < q.val
      apply (E.before_iff_slot_lt i p q).mp
      rw [hp.1]
      exact ha.2
  · intro a b ha hb hab
    have ha' := (Classical.choose_spec
      ((mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a x.property).mp ha.1)).1
    have hb' := (Classical.choose_spec
      ((mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i b x.property).mp hb.1)).1
    exact ha'.symm.trans ((congrArg (E.event i) hab).trans hb')
  · intro p hp
    have hFoot : x.val ∈ cofinalEventFootprint E (E.event i p) :=
      ⟨i,p,rfl,mem_image_of_mem _ hp.1⟩
    refine ⟨E.event i p,⟨hFoot,(E.before_iff_slot_lt i p q).mpr hp.2⟩,?_⟩
    apply E.injective i
    exact (Classical.choose_spec
      ((mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i (E.event i p) x.property).mp hFoot)).1

open scoped Manifold ContDiff
open HironakaG3EmptyAwareHistory

theorem cofinal_pointCount_eq_of_physical_comparison
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (E : CofinalEvents c I)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (i j : ℕ)
    (φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c j).U)
    (ψ : (c i).Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c j).Y)
    (h : EmptyAwareTowerIso φ (c i).T (c j).T ψ)
    (q : {k // Occupied (c i).T k})
    (hEvent : E.event j (occupiedComparison h q) = E.event i q) (x : (c i).U) :
    pointCount (cofinalEventFootprint E) E.Before x.val (E.event i q) =
      pointCount (cofinalEventFootprint E) E.Before (φ x).val (E.event i q) := by
  rw [cofinal_pointCount_eq_chart E cmp hMono hLift i x q,← hEvent,
    cofinal_pointCount_eq_chart E cmp hMono hLift j (φ x) (occupiedComparison h q)]
  apply pointCount_orderIso _ _ (occupiedComparison h)
  intro a
  rw [slotFootprint_occupiedComparison h a]
  rfl

theorem cofinal_rank_of_point_count_constancy
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (E : CofinalEvents c I)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hConstant : ∀ a x y, x ∈ cofinalEventFootprint E a → y ∈ cofinalEventFootprint E a →
      pointCount (cofinalEventFootprint E) E.Before x a =
        pointCount (cofinalEventFootprint E) E.Before y a) :
    ∃ rank : I → ℕ, ∀ {a b}, SpatialBefore E a b → rank a < rank b := by
  have hLF := locallyFinite_cofinal_eventFootprints E cmp hMono hLift hCover
  have hNonempty (a : I) : (cofinalEventFootprint E a).Nonempty := by
    obtain ⟨i,p,hp⟩ := hOccurs a
    obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c i).T p.val).mpr p.property
    exact ⟨x.val,i,p,hp,mem_image_of_mem _ hx⟩
  obtain ⟨rank,hRank⟩ := exists_rank_of_point_count_constancy
    (cofinalEventFootprint E) E.Before (fun ha hb => E.before_trans ha hb)
    E.before_irrefl hLF.point_finite hNonempty hConstant
  refine ⟨rank,fun {_ _} h => ?_⟩
  obtain ⟨ha,hb⟩ := (spatialBefore_iff_before_and_footprint_meets E cmp hMono hLift).mp h
  exact hRank ha hb

open TopologicalSpace Hironaka.BlowupSequences BlowupTowerTransforms

/-- Restricting the base keeps the exact count of earlier occupied
slots through a point for any selected slot seen on that open. -/
theorem pointCount_restrict
    {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y) (U : Opens X)
    (x : U) (p : {k // Occupied (restrict U T) k}) :
    pointCount (fun a : {k // Occupied T k} => slotFootprint T a.val)
      (· < ·) x.val (occupiedRestrictionEmbedding U T p) =
    pointCount (fun a : {k // Occupied (restrict U T) k} => slotFootprint (restrict U T) a.val)
      (· < ·) x p := by
  symm
  let f := occupiedRestrictionEmbedding U T
  apply Set.ncard_congr (fun a _ => f a)
  · intro a ha
    have hMem : x ∈ slotFootprint (restrict U T) a.val := ha.1
    rw [slotFootprint_restrict] at hMem
    exact ⟨hMem, f.strictMono ha.2⟩
  · intro a b _ _ hab
    exact f.injective hab
  · intro a ha
    have hMem : x.val ∈ slotFootprint T a.val := ha.1
    let a' : {k // Occupied (restrict U T) k} :=
      ⟨a.val, (occupied_restrict_iff_slotFootprint_meets T U a.val).mpr ⟨x.val,hMem,x.property⟩⟩
    have hOrd : a' < p := ha.2
    have hMem' : x ∈ slotFootprint (restrict U T) a'.val := by
      rw [slotFootprint_restrict]
      exact hMem
    exact ⟨a',⟨hMem',hOrd⟩,Subtype.ext rfl⟩

/-- A comparison between two genuine local restrictions may move the base
point. It preserves the derived count when it carries the chosen event. -/
theorem cofinal_pointCount_eq_of_restricted_comparison
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (E : CofinalEvents c I)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (i j : ℕ) (U : Opens (c i).U) (V : Opens (c j).U)
    (φ : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (ψ : openPreimage (c i).T U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      openPreimage (c j).T V)
    (h : EmptyAwareTowerIso φ (restrict U (c i).T) (restrict V (c j).T) ψ)
    (p : {k // Occupied (restrict U (c i).T) k}) (x : U)
    (hEvent : E.event j (occupiedRestrictionEmbedding V (c j).T (occupiedComparison h p)) =
      E.event i (occupiedRestrictionEmbedding U (c i).T p)) :
    pointCount (cofinalEventFootprint E) E.Before x.val.val
        (E.event i (occupiedRestrictionEmbedding U (c i).T p)) =
      pointCount (cofinalEventFootprint E) E.Before (φ x).val.val
        (E.event i (occupiedRestrictionEmbedding U (c i).T p)) := by
  rw [cofinal_pointCount_eq_chart E cmp hMono hLift i x.val
    (occupiedRestrictionEmbedding U (c i).T p), ← hEvent,
    cofinal_pointCount_eq_chart E cmp hMono hLift j (φ x).val
      (occupiedRestrictionEmbedding V (c j).T (occupiedComparison h p)),
    pointCount_restrict, pointCount_restrict]
  apply pointCount_orderIso _ _ (occupiedComparison h)
  intro a
  rw [slotFootprint_occupiedComparison h a]
  rfl

/-- A local comparison of two sightings of a selected cofinal event. -/
structure LocalPointComparison
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (E : CofinalEvents c I) (a : I) (x y : X) where
  leftIndex : ℕ
  rightIndex : ℕ
  leftOpen : Opens (c leftIndex).U
  rightOpen : Opens (c rightIndex).U
  base : leftOpen ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ rightOpen
  endpoint : openPreimage (c leftIndex).T leftOpen ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
    openPreimage (c rightIndex).T rightOpen
  compare : EmptyAwareTowerIso base (restrict leftOpen (c leftIndex).T)
    (restrict rightOpen (c rightIndex).T) endpoint
  slot : {k // Occupied (restrict leftOpen (c leftIndex).T) k}
  point : leftOpen
  point_eq : point.val.val = x
  base_point_eq : (base point).val.val = y
  left_event : E.event leftIndex (occupiedRestrictionEmbedding leftOpen (c leftIndex).T slot) = a
  right_event : E.event rightIndex
    (occupiedRestrictionEmbedding rightOpen (c rightIndex).T (occupiedComparison compare slot)) = a

/-- Local comparisons that carry a selected event between any two points
of its footprint suffice for a common weak spatial rank. -/
theorem cofinal_rank_of_local_point_comparisons
    {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (E : CofinalEvents c I)
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hCompare : ∀ a x y, x ∈ cofinalEventFootprint E a → y ∈ cofinalEventFootprint E a →
      Nonempty (LocalPointComparison E a x y)) :
    ∃ rank : I → ℕ, ∀ {a b}, SpatialBefore E a b → rank a < rank b := by
  apply cofinal_rank_of_point_count_constancy E cmp hMono hLift hCover hOccurs
  intro a x y hx hy
  obtain ⟨B⟩ := hCompare a x y hx hy
  have hCount := cofinal_pointCount_eq_of_restricted_comparison E cmp hMono hLift
    B.leftIndex B.rightIndex B.leftOpen B.rightOpen B.base B.endpoint B.compare B.slot B.point
    (B.right_event.trans B.left_event.symm)
  simpa only [B.point_eq,B.base_point_eq,B.left_event] using hCount

end Hironaka.HironakaG8CofinalLocalPointRank
