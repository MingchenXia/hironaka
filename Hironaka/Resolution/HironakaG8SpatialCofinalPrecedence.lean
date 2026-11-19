import Hironaka.Resolution.HironakaG8PhysicalChartOccupiedLifts
import Hironaka.Resolution.HironakaG8InjectiveFiniteAncestryRank

/-! Physical cofinal precedence supported on intersecting centre footprints. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SpatialCofinalPrecedence
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass MaxLocusLocal
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison HironakaG8PhysicalChartOccupiedLifts
  G3UniversePhysicalClassComparisons HironakaG8InjectiveFiniteAncestryRank

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}

/-- The projected occurrence is a subset of the common original manifold. -/
def chartSlotFootprint (c : TowerChart K Z P) (p : {k // Occupied c.T k}) : Set X :=
  (Subtype.val : c.U → X) '' slotFootprint c.T p.val

/-- Literal stage footprints restrict exactly under the actual occupied lift. -/
theorem chartSlotFootprint_lift (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) (p : {k // Occupied c.T k}) :
    chartSlotFootprint c p =
      chartSlotFootprint d (chartOccupiedLift cmp c d h p) ∩ (c.U : Set X) := by
  let V := nestedOpens d.U (c.U ⊓ d.U)
  obtain ⟨φ,hφ,ψ,hCmp⟩ := physical_comparison_nested_chart cmp c d h
  have hL : occupiedLiftOnOpen V d.T hCmp = chartOccupiedLift cmp c d h := by
    apply occupied_orderEmbedding_unique_of_range (T := c.T) (S := d.T)
    ext q
    rw [mem_range_occupiedLiftOnOpen]
    unfold chartOccupiedLift
    rw [mem_range_occupiedLiftOnOpen]
  have hF := slotFootprint_occupiedComparison hCmp p
  rw [slotFootprint_restrict] at hF
  rw [← hL]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    have ha' : (φ a).val ∈ slotFootprint d.T (occupiedLiftOnOpen V d.T hCmp p).val := by
      rw [hF] at ha
      exact ha
    exact ⟨⟨(φ a).val,ha',hφ a⟩,a.property⟩
  · rintro ⟨⟨b,hb,rfl⟩,hbC⟩
    let a : c.U := ⟨b.val,hbC⟩
    have ha : (φ a).val = b := Subtype.ext (hφ a)
    refine ⟨a,?_,rfl⟩
    rw [hF]
    change (φ a).val ∈ slotFootprint d.T (occupiedLiftOnOpen V d.T hCmp p).val
    rwa [ha]

variable {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)

/-- The actual cofinal footprint is the union of projected occurrences
carrying the same event. -/
def cofinalEventFootprint (a : ι) : Set X :=
  {x | ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a ∧ x ∈ chartSlotFootprint (c i) p}

/-- Retain only precedence between two actual ordered occurrences
whose projected footprints meet in a common chart. -/
def SpatialBefore (a b : ι) : Prop :=
  ∃ (i : ℕ) (p q : {k // Occupied (c i).T k}), E.event i p = a ∧ E.event i q = b ∧
    p.val < q.val ∧ (chartSlotFootprint (c i) p ∩ chartSlotFootprint (c i) q).Nonempty

theorem spatialBefore_imp_before {a b : ι} (h : SpatialBefore E a b) : E.Before a b := by
  obtain ⟨i,p,q,hp,hq,hlt,_⟩ := h
  exact ⟨i,p,q,hp,hq,hlt⟩

/-- Cohesive literal lifts make the common-chart rule equivalent to
precedence with intersection of the whole actual cofinal footprints. -/
theorem spatialBefore_iff_before_and_footprint_meets
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    {a b : ι} :
    SpatialBefore E a b ↔ E.Before a b ∧
      (cofinalEventFootprint E a ∩ cofinalEventFootprint E b).Nonempty := by
  constructor
  · rintro ⟨i,p,q,hp,hq,hlt,x,hxP,hxQ⟩
    exact ⟨⟨i,p,q,hp,hq,hlt⟩,x,⟨i,p,hp,hxP⟩,⟨i,q,hq,hxQ⟩⟩
  · rintro ⟨⟨i,p,q,hp,hq,hlt⟩,x,⟨j,r,hr,hxr⟩,⟨k,s,hs,hxs⟩⟩
    let m := max i (max j k)
    let hi : i ≤ m := le_max_left _ _
    let hj : j ≤ m := (le_max_left j k).trans (le_max_right i (max j k))
    let hk : k ≤ m := (le_max_right j k).trans (le_max_right i (max j k))
    have hrp : E.lift hj r = E.lift hi p :=
      E.injective m (by rw [E.lift_event,E.lift_event,hr,hp])
    have hsq : E.lift hk s = E.lift hi q :=
      E.injective m (by rw [E.lift_event,E.lift_event,hs,hq])
    have hmem {u : ℕ} (hu : u ≤ m) (t : {k // Occupied (c u).T k})
        (ht : x ∈ chartSlotFootprint (c u) t) :
        x ∈ chartSlotFootprint (c m) (E.lift hu t) := by
      rw [hLift]
      have hTrace := chartSlotFootprint_lift cmp (c u) (c m) (hMono hu) t
      rw [hTrace] at ht
      exact ht.1
    refine ⟨m,E.lift hi p,E.lift hi q,(E.lift_event hi p).trans hp,(E.lift_event hi q).trans hq,
      E.lift_mono hi hlt,x,?_,?_⟩
    · rw [← hrp]
      exact hmem hj r hxr
    · rw [← hsq]
      exact hmem hk s hxs

/-- An event is visible on a chart exactly when its whole projected
footprint meets that chart. For points in the chart the occurrence gives
the exact trace, even if the original witness came from a larger chart. -/
theorem mem_cofinalEventFootprint_iff_chart
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (i : ℕ) (a : ι) {x : X} (hx : x ∈ (c i).U) :
    x ∈ cofinalEventFootprint E a ↔
      ∃ p : {k // Occupied (c i).T k}, E.event i p = a ∧ x ∈ chartSlotFootprint (c i) p := by
  refine ⟨?_,fun ⟨p,hp,hxp⟩ => ⟨i,p,hp,hxp⟩⟩
  rintro ⟨j,q,hq,hxq⟩
  let m := max i j
  let hi : i ≤ m := le_max_left _ _
  let hj : j ≤ m := le_max_right _ _
  let r := E.lift hj q
  have hxr : x ∈ chartSlotFootprint (c m) r := by
    change x ∈ chartSlotFootprint (c m) (E.lift hj q)
    rw [hLift]
    exact (chartSlotFootprint_lift cmp (c j) (c m) (hMono hj) q ▸ hxq).1
  obtain ⟨y,hy,rfl⟩ := hxr
  let O := nestedOpens (c m).U ((c i).U ⊓ (c m).U)
  have hyO : y ∈ O := ⟨hx,y.property⟩
  have hOcc : Occupied (restrict O (c m).T) r.val :=
    (occupied_restrict_iff_slotFootprint_meets (c m).T O r.val).mpr ⟨y,hy,hyO⟩
  have hRange : r ∈ range (chartOccupiedLift cmp (c i) (c m) (hMono hi)) := by
    unfold chartOccupiedLift
    rw [mem_range_occupiedLiftOnOpen]
    exact hOcc
  obtain ⟨p,hp⟩ := hRange
  have hp' : E.lift hi p = r := (hLift hi p).trans hp
  refine ⟨p,?_,?_⟩
  · calc
      E.event i p = E.event m (E.lift hi p) := (E.lift_event hi p).symm
      _ = E.event m r := congrArg (E.event m) hp'
      _ = a := (E.lift_event hj q).trans hq
  · rw [chartSlotFootprint_lift cmp (c i) (c m) (hMono hi) p,hp]
    exact ⟨⟨y,hy,rfl⟩,hx⟩

/-- The projected event supports are locally finite on the base of any
covering monotone chain of actual charts with the physical lifts. -/
theorem locallyFinite_cofinal_eventFootprints
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) : LocallyFinite (cofinalEventFootprint E) := by
  intro x
  obtain ⟨i,hi⟩ := hCover x
  let f : {k // Occupied (c i).T k} → Fin (c i).T.length :=
    fun p => ⟨p.val,occupied_lt_length _ p.property⟩
  let _ : Finite {k // Occupied (c i).T k} := Finite.of_injective f (fun _ _ h => Subtype.ext
    (congrArg Fin.val h))
  refine ⟨(c i).U,(c i).U.isOpen.mem_nhds hi, (finite_range (E.event i)).subset ?_⟩
  rintro a ⟨y,hy,hyU⟩
  obtain ⟨p,hp,_⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a hyU).mp hy
  exact ⟨p,hp⟩

/-- A compact whole event footprint has only finitely many incoming
spatial edges. This condition can be applied one event at a time. -/
theorem finite_spatial_incoming_of_compact
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) {b : ι}
    (hCompact : IsCompact (cofinalEventFootprint E b)) : {a | SpatialBefore E a b}.Finite := by
  have hLF := locallyFinite_cofinal_eventFootprints E cmp hMono hLift hCover
  refine (hLF.finite_nonempty_inter_compact hCompact).subset ?_
  intro a hab
  exact ((spatialBefore_iff_before_and_footprint_meets E cmp hMono hLift).mp hab).2

/-- A well-founded incoming spatial relation of finite branching gives
distinct natural slots, compatible with every intersecting ordered pair
in every actual chart. Disjoint pairs carry no comparison requirement. -/
theorem exists_injective_rank_of_spatial_incoming
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hWF : WellFounded (SpatialBefore E)) (hFinite : ∀ b, {a | SpatialBefore E a b}.Finite) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧
      (∀ ⦃a b⦄, Relation.TransGen (SpatialBefore E) a b → rank a < rank b) ∧
      ∀ i (p q : {k // Occupied (c i).T k}), p.val < q.val →
        (chartSlotFootprint (c i) p ∩ chartSlotFootprint (c i) q).Nonempty →
          rank (E.event i p) < rank (E.event i q) := by
  let _ : Countable ι := cofinal_events_countable E hOccurs
  obtain ⟨rank,hInj,hRank⟩ := exists_injective_rank_of_finite_incoming hWF hFinite
  exact ⟨rank,hInj,hRank,fun i p q hpq hMeet =>
    hRank (.single ⟨i,p,q,rfl,rfl,hpq,hMeet⟩)⟩

end Hironaka.HironakaG8SpatialCofinalPrecedence
