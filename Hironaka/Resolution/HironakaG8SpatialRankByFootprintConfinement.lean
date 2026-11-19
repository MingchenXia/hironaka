import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

/-! Spatial rank from compact localization of incoming trajectories. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG8SpatialRankByFootprintConfinement

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8SpatialCofinalPrecedence HironakaG8InjectiveFiniteAncestryRank
  HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)

theorem before_of_spatial_ancestry {a b : ι}
    (h : Relation.TransGen (SpatialBefore E) a b) : E.Before a b := by
  induction h with
  | single h => exact spatialBefore_imp_before E h
  | tail _ h ih => exact E.before_trans ih (spatialBefore_imp_before E h)

/-- A compact transversal for the entire incoming spatial ancestry, even
for noncompact events, provides the injective physical rank. -/
theorem exists_injective_spatial_rank_of_compact_ancestral_transversals
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hCompact : ∀ b, ∃ C : Set X, IsCompact C ∧
      ∀ a, Relation.TransGen (SpatialBefore E) a b →
        (cofinalEventFootprint E a ∩ C).Nonempty) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧
      ∀ ⦃a b⦄, Relation.TransGen (SpatialBefore E) a b → rank a < rank b := by
  let _ : Countable ι := cofinal_events_countable E hOccurs
  apply exists_injective_rank_of_finite_predecessors (before := Relation.TransGen (SpatialBefore E))
    (fun {_ _ _} h₁ h₂ => Relation.TransGen.trans h₁ h₂)
    (fun b h => E.before_irrefl b (before_of_spatial_ancestry E h))
  intro b
  obtain ⟨C,hC,hReach⟩ := hCompact b
  have hLF := locallyFinite_cofinal_eventFootprints E cmp hMono hLift hCover
  exact (hLF.finite_nonempty_inter_compact hC).subset (fun a ha => hReach a ha)

/-- For actual covering cofinal charts, the existence of a spatial
rank is precisely compact confinement of a choice of representatives
for the predecessors of every event. -/
theorem exists_injective_spatial_rank_iff_compact_ancestral_transversals
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a) :
    (∃ rank : ι → ℕ, Function.Injective rank ∧ ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b) ↔
    ∀ b, ∃ C : Set X, IsCompact C ∧
      ∀ a, Relation.TransGen (SpatialBefore E) a b →
        (cofinalEventFootprint E a ∩ C).Nonempty := by
  constructor
  · rintro ⟨rank,hRank,hr⟩ b
    have hAnc {a b : ι} (h : Relation.TransGen (SpatialBefore E) a b) : rank a < rank b := by
      induction h with
      | single h => exact hr h
      | tail _ h ih => exact ih.trans (hr h)
    have hNonempty (a : ι) : (cofinalEventFootprint E a).Nonempty := by
      obtain ⟨i,p,hp⟩ := hOccurs a
      obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c i).T p.val).mpr p.property
      exact ⟨x.val,i,p,hp,mem_image_of_mem _ hx⟩
    choose rep hRep using hNonempty
    let anc := {a | Relation.TransGen (SpatialBefore E) a b}
    have hFinite : anc.Finite :=
      ((finite_Iio (rank b)).preimage hRank.injOn).subset fun _ ha => hAnc ha
    exact ⟨rep '' anc,(hFinite.image rep).isCompact,fun a ha =>
      ⟨rep a,hRep a,mem_image_of_mem _ ha⟩⟩
  · intro hCompact
    obtain ⟨rank,hInj,hRank⟩ :=
      exists_injective_spatial_rank_of_compact_ancestral_transversals E cmp hMono hLift hCover hOccurs hCompact
    exact ⟨rank,hInj,fun {_ _} h => hRank (.single h)⟩

/-- If earlier intersecting events contain the later footprint, every
incoming ancestry is confined to the charts at any point of that footprint.
Compactness of the whole original singular component is unnecessary. -/
theorem exists_injective_spatial_rank_of_reverse_footprint_nesting
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hNest : ∀ a b, SpatialBefore E a b → cofinalEventFootprint E b ⊆ cofinalEventFootprint E a) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧
      ∀ ⦃a b⦄, Relation.TransGen (SpatialBefore E) a b → rank a < rank b := by
  apply exists_injective_spatial_rank_of_compact_ancestral_transversals E cmp hMono hLift hCover hOccurs
  intro b
  obtain ⟨i,p,hp⟩ := hOccurs b
  obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c i).T p.val).mpr p.property
  have hxB : x.val ∈ cofinalEventFootprint E b := ⟨i,p,hp,mem_image_of_mem _ hx⟩
  refine ⟨{x.val},isCompact_singleton,fun a h => ⟨x.val,?_,mem_singleton _⟩⟩
  have hSub {a b : ι} (h : Relation.TransGen (SpatialBefore E) a b) :
      cofinalEventFootprint E b ⊆ cofinalEventFootprint E a := by
    induction h with
    | single h => exact hNest _ _ h
    | tail _ h ih => exact (hNest _ _ h).trans ih
  exact hSub h hxB

end Hironaka.HironakaG8SpatialRankByFootprintConfinement
