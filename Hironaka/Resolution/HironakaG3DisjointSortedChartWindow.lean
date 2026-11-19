import Hironaka.Resolution.HironakaG3SortedLocalWindowGeometry
import Hironaka.Resolution.HironakaG3FiniteVisibleAtlas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointSortedChartWindow
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3SortedLocalWindowGeometry HironakaDisjointFiniteControlledHistory
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) {P : Z → X}

def disjointSortedWindowWitness
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) (L : Finset κ) : Prop :=
  (∀ j, (D j ∩ (c.U : Set X)).Nonempty → j ∈ L) ∧
  let E := ((L.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·)
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  IsSNCDivisor n (geoTransformAlong (fullMarked E J) c.T).E ∧
    ((∃ i, c.U ≤ W i ∧ K i c.U c.Y c.T ∧
      HasNormalCrossings n (strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' C i))
        (geoTransformAlong (fullMarked E J) c.T).E) ∨
      ((c.U : Set X) ⊆ (⋃ i, C i)ᶜ ∧ IsEmptyTower c.T))

theorem exists_disjoint_sorted_chart_window (hD : IsLocallyFiniteSNCDivisor n D)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i))
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) :
    ∃ L, disjointSortedWindowWitness C D W K c L := by
  obtain ⟨R,hVis⟩ := c.mem.2
  rcases c.mem.1 with ⟨i,hUW,hK⟩ | ⟨hAvoid,hEmpty⟩
  · obtain ⟨L,hL,hSNC,hNC⟩ := hGeo i c.U c.Y c.T hK R hVis
    exact ⟨L,hL,hSNC,Or.inl ⟨i,hUW,hK,hNC⟩⟩
  · exact ⟨R,hVis,empty_tower_sorted_window_snc D hD R c.U c.T hEmpty,Or.inr ⟨hAvoid,hEmpty⟩⟩

def disjointSortedChartWindow (hD : IsLocallyFiniteSNCDivisor n D)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i))
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) : Finset κ :=
  Classical.choose (exists_disjoint_sorted_chart_window C D W K hD hGeo c)

theorem disjoint_sorted_chart_window_spec (hD : IsLocallyFiniteSNCDivisor n D)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i))
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) :
    disjointSortedWindowWitness C D W K c (disjointSortedChartWindow C D W K hD hGeo c) :=
  Classical.choose_spec (exists_disjoint_sorted_chart_window C D W K hD hGeo c)
end
end Hironaka.HironakaG3DisjointSortedChartWindow
