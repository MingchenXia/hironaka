import Hironaka.Resolution.HironakaG8CofinalRoundFootprints
import Hironaka.Resolution.HironakaG8WeakSpatialRankByEpoch

/-! One original-source open controls all visible events at each round. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG8RoundPointVisibility

/-- At a point, a locally finite closed family has a single open
whose visible sets are exactly the sets containing that point. -/
theorem exists_open_exact_footprint_visibility
    {X ι : Type*} [TopologicalSpace X] (F : ι → Set X)
    (hLF : LocallyFinite F) (hClosed : ∀ i, IsClosed (F i)) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ i, (F i ∩ (U : Set X)).Nonempty ↔ x ∈ F i := by
  obtain ⟨O,hO,hOpen,hx⟩ := mem_nhds_iff.mp (hLF.iInter_compl_mem_nhds hClosed x)
  refine ⟨⟨O,hOpen⟩,hx,fun i => ⟨?_,fun hi => ⟨x,hi,hx⟩⟩⟩
  rintro ⟨y,hy,hyO⟩
  by_contra hi
  exact (mem_iInter₂.mp (hO hyO) i hi) hy

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8SpatialCofinalPrecedence HironakaG8WeakSpatialRankByEpoch
  HironakaG8CofinalRoundFootprints

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- A single point window sees at most one actual cofinal event at each
weak rank, simultaneously for the entire original family. -/
theorem exists_open_with_one_footprint_per_round
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (rank : ι → ℕ) (hRank : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b)
    (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      (∀ a, (cofinalEventFootprint E a ∩ (U : Set X)).Nonempty ↔ x ∈ cofinalEventFootprint E a) ∧
      ∀ a b, (cofinalEventFootprint E a ∩ (U : Set X)).Nonempty →
        (cofinalEventFootprint E b ∩ (U : Set X)).Nonempty → rank a = rank b → a = b := by
  obtain ⟨U,hx,hVisible⟩ := exists_open_exact_footprint_visibility (cofinalEventFootprint E)
    (locallyFinite_cofinal_eventFootprints E cmp hMono hLift hCover)
    (isClosed_cofinalEventFootprint E cmp hMono hLift hCover) x
  refine ⟨U,hx,hVisible,?_⟩
  intro a b ha hb hr
  by_contra hNe
  have hDisj := disjoint_cofinalEventFootprints_of_weak_rank_eq E cmp hMono hLift hOccurs
    rank hRank hNe hr
  exact Set.disjoint_left.mp hDisj ((hVisible a).mp ha) ((hVisible b).mp hb)

end Hironaka.HironakaG8RoundPointVisibility
