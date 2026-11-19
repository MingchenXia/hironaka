import Hironaka.Resolution.HironakaG8PackedRoundChart

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8PackedRoundFamily

open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8OccupiedSlotComparison HironakaG8FinitePartitionPacking
  HironakaG8SortedRankExactPacking HironakaG8PackedRoundChart

variable {n : ℕ} {X Y : ℕ → CMfd.{0} n}

/-- Data of the actual packed cofinal family, retaining the exact
intermediate block geometry and terminal objects of the sorted family. -/
structure PackedRoundFamily (T : ∀ i, BlowupTower (X i) (Y i))
    (roundFoot : ∀ i, ℕ → Set (X i)) (M : ∀ i, MarkedIdeal n (X i))
    (W : ∀ i, Set (X i)) where
  tower : ∀ i, BlowupTower (X i) (Y i)
  labels : ℕ → List ℕ
  packing : ∀ i, BlockPacking (X i) (T i) (tower i) ((labels i).map (roundFoot i))
  sorted : ∀ i, (labels i).Pairwise (· < ·)
  labels_iff : ∀ i r, r ∈ labels i ↔ (roundFoot i r).Nonempty
  length_eq_labels : ∀ i, (tower i).length = (labels i).length
  readback : ∀ i j r, (labels i)[j]? = some r → slotFootprint (tower i) j = roundFoot i r
  occupied : ∀ i j, (slotFootprint (tower i) j).Nonempty ↔ j < (labels i).length
  proj_eq : ∀ i, (tower i).proj = (T i).proj
  test : ∀ i, IsGeoTestTower (M i) (tower i)
  singular : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
    (strictTransform n P.proj (W i))) (tower i)
  smooth : ∀ i, IsClosedSubmanifold n (strictTransform n (tower i).proj (W i))

/-- Pack every sorted chart on its actual intermediate block endpoints. -/
theorem exists_packed_round_family {α : ℕ → Type*}
    (T : ∀ i, BlowupTower (X i) (Y i)) (order : ∀ i, List (α i)) (rank : ∀ i, α i → ℕ)
    (roundFoot : ∀ i, ℕ → Set (X i))
    (hLen : ∀ i, (T i).length = (order i).length)
    (hOccupied : ∀ i j, (slotFootprint (T i) j).Nonempty ↔ j < (order i).length)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank i p ≤ rank i q))
    (hDisj : ∀ i j k p q, j ≠ k → (order i)[j]? = some p → (order i)[k]? = some q →
      rank i p = rank i q → Disjoint (slotFootprint (T i) j) (slotFootprint (T i) k))
    (hRound : ∀ i r, rankFootprint (T i) (orderRank (order i) (rank i)) r = roundFoot i r)
    (M : ∀ i, MarkedIdeal n (X i)) (hM : ∀ i, (M i).IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (M i) (T i))
    (W : ∀ i, Set (X i))
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj (W i))) (T i))
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (T i).proj (W i))) :
    Nonempty (PackedRoundFamily T roundFoot M W) := by
  classical
  have hPack i := pack_round_chart (T i) (order i) (rank i) (roundFoot i) (hLen i)
    (hOccupied i) (hSorted i) (hDisj i) (hRound i) (M i) (hM i) (hTest i)
    (W i) (hSing i) (hSmooth i)
  choose G labels hPacking hSorted' hLabels hLength hRead hOccup hProj hGTest hGSing hGSmooth
    using hPack
  exact ⟨⟨G,labels,hPacking,hSorted',hLabels,hLength,hRead,hOccup,hProj,
    hGTest,hGSing,hGSmooth⟩⟩

end Hironaka.HironakaG8PackedRoundFamily
