import Hironaka.Resolution.HironakaG4OrderedMaskStrictEquivariance
import Hironaka.Resolution.HironakaG4OrderedRowCode

/-! A fixed order of original masks for the canonical compact-relative finish. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ProcessedMaskIncidenceOrder

noncomputable section

open Hironaka.BlowupSequences BlowupTowers
  NormalCrossings HironakaG4OrderedRowCode HironakaActualProcessedAllMasksDrop
  HironakaG4RelativeOrderedProcessedFinish

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- At one count level, order the masks by the incidence vector of their
original old rows, with the earliest row as the first lexicographic digit. -/
def orderedMaskLevel (r q : ℕ) : List (Finset (Fin r)) :=
  (((Finset.univ : Finset (Fin r)).powersetCard q).toList).mergeSort
    (fun P Q => decide (orderedRowTieCode (fun _ => 0) P ≤ orderedRowTieCode (fun _ => 0) Q))

/-- The fixed incidence order visits exactly the masks of the given count. -/
theorem orderedMaskLevel_toFinset (r q : ℕ) :
    (orderedMaskLevel r q).toFinset = (Finset.univ : Finset (Fin r)).powersetCard q := by
  ext P
  simp [orderedMaskLevel]

/-- The actual ordered finish may use the original incidence order at
every count level, independently of the local stages and compact set. -/
theorem exists_incidence_ordered_processed_finish_near (hn : 0 < n)
    {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) {q : ℕ} (hAt : At W E q T) (K : Set X) (hK : IsCompact K) :
    OrderedProcessedFinishNear hn W E T id (descendingMaskLabels (orderedMaskLevel E.length) q) K :=
  exists_ordered_processed_finish_near hn (orderedMaskLevel E.length) q hW hE hdense T hAt id
    (fun j => by simpa only [List.map_id] using orderedMaskLevel_toFinset E.length j) K hK

end
end Hironaka.HironakaG4ProcessedMaskIncidenceOrder
