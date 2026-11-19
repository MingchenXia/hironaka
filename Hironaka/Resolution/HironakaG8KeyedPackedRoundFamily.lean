import Hironaka.Resolution.HironakaG8PackedRoundFamily
import Hironaka.Resolution.HironakaG8CofinalSpatialRankEndpoint
import Hironaka.Resolution.HironakaG8KeyedRoundReadback

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8KeyedPackedRoundFamily

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  HironakaG3RTowerClass HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8CofinalSpatialRankEndpoint HironakaG8CofinalRoundFootprints
  HironakaG8KeyedRoundReadback HironakaG8PackedRoundFamily

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  {c : ℕ → TowerChart K Z P} {ι κ : Type*} [LinearOrder κ]

/-- The actual weak-rank sorted cofinal charts give their entire packed
round family using the exact literal round-footprint dictionary. -/
theorem exists_keyed_packed_round_family
    (E : CofinalEvents c ι) {key : ι → κ} {M : MarkedIdeal n X} {W : Set X}
    (D : CofinalKeyedSingularWords E key M W) (rank : ι → ℕ) (hM : M.IsWellFormed)
    (hSorted : ∀ i, (D.order i).Pairwise (fun p q => rank (E.event i p) ≤ rank (E.event i q)))
    (hDisj : ∀ i j k p q, j ≠ k → (D.order i)[j]? = some p → (D.order i)[k]? = some q →
      rank (E.event i p) = rank (E.event i q) →
        Disjoint (slotFootprint (D.R i) j) (slotFootprint (D.R i) k)) :
    Nonempty (PackedRoundFamily D.R (fun i r => chartRoundFootprint E rank r i)
      (fun i => MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
      (fun i => (Subtype.val : (c i).U → X) ⁻¹' W)) :=
  exists_packed_round_family D.R D.order (fun i p => rank (E.event i p))
    (fun i r => chartRoundFootprint E rank r i) D.length_eq_order D.occupied hSorted hDisj
    (chartRankFootprint_eq E D rank)
    _ (fun i => IsWellFormed.pullback_val hM (c i).U) D.test _ D.singular D.smooth

end Hironaka.HironakaG8KeyedPackedRoundFamily
