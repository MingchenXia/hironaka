import Hironaka.Resolution.HironakaG3SortedLocalWindowGeometry
import Hironaka.Resolution.HironakaG3CanonicalWindowPermutation
import Hironaka.Resolution.HironakaG3SNCListPermutation
import Hironaka.Resolution.HironakaG3IndexedResidualFullHeadGeometry
import Hironaka.Resolution.HironakaG3IndexedResidualFixedHeadClass
import Hironaka.Resolution.HironakaG3SeparatedVisibleChartWindow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualSortedWindowGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsComparison
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3IndexedResidualFullHeadGeometry HironakaG3IndexedResidualFixedHeadClass
  HironakaG3SortedLocalWindowGeometry HironakaG3CanonicalWindowPermutation HironakaG3SNCListPermutation
  HironakaG3SeparatedVisibleChartWindow HironakaDisjointFiniteControlledHistory

theorem indexed_residual_sorted_local_window_geometry {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d) :
    HasSortedLocalWindowGeometry C D (residualFixedHead (canonicalContact C D hC.nonempty hD.1)
      hNc hN C r D (containingLabels C D hC.nonempty hD.1)) := by
  intro U Y T hT R₀ _hR₀
  obtain ⟨R,hDis,hVis,hHead⟩ := hT
  let S := containingLabels C D hC.nonempty hD.1
  refine ⟨R ∪ S,?_,?_⟩
  · intro j hj
    by_cases hjS : j ∈ S
    · exact Finset.mem_union_right _ hjS
    · exact Finset.mem_union_left _ (hVis j hjS hj)
  · let D' : κ → Set U := fun j => (Subtype.val : U → X) ⁻¹' D j
    let J := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) (∅ : Set X))
    let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) C)
    let E := ((R.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·)
    let Es := (((R ∪ S).sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·)
    have hg := indexed_residual_full_head_geometry hd ht C D hC hD hr hpure hNc hN R hDis U Y T hHead
    have hp : (geoTransformAlong (fullMarked E Jx) T).E.Perm
        (geoTransformAlong (fullMarked Es Jx) T).E := by
      simpa [D',E,Es,List.map_append,List.map_map,Function.comp_def] using
        residual_containing_sorted_union_transform_perm D' R S hDis Jx T
    have hSNC : IsSNCDivisor (d+t) (geoTransformAlong (fullMarked Es Jx) T).E := by
      exact isSNCDivisor_of_perm hg.2.1 hp.symm
    have hNC : HasNormalCrossings (d+t) (strictTransform (d+t) T.proj ((Subtype.val : U → X) ⁻¹' C))
        (geoTransformAlong (fullMarked Es Jx) T).E :=
      hasNormalCrossings_of_forall_mem hg.2.2.2.2 hp.symm.subset
    have heq := transformed_boundary_independent_of_ideal Es J Jx T
    change IsSNCDivisor (d+t) (geoTransformAlong (fullMarked Es J) T).E ∧
      HasNormalCrossings (d+t) (strictTransform (d+t) T.proj ((Subtype.val : U → X) ⁻¹' C))
        (geoTransformAlong (fullMarked Es J) T).E
    rw [heq]
    exact ⟨hSNC,hNC⟩
end
end Hironaka.HironakaG3ResidualSortedWindowGeometry
