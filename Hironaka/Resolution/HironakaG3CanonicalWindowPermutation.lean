import Hironaka.Resolution.HironakaG3IndexedResidualFullWindow
import Hironaka.Resolution.HironakaDisjointFiniteControlledHistory
import Hironaka.Resolution.HironakaG4PermutedFullTest
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CanonicalWindowPermutation
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaDisjointFiniteControlledHistory HironakaG4PermutedFullTest

/-- Sorting a complete residual-and-containing window globally changes only
its label order, preserving each label occurrence. -/
theorem residual_containing_sorted_union_perm {ι : Type*} [LinearOrder ι] (R S : Finset ι)
    (hDis : Disjoint S R) :
    (R.sort (· ≤ ·) ++ S.sort (· ≤ ·)).Perm ((R ∪ S).sort (· ≤ ·)) := by
  have hdis : List.Disjoint (R.sort (· ≤ ·)) (S.sort (· ≤ ·)) := by
    apply List.disjoint_left.mpr
    intro i hiR hiS
    have hiR' : i ∈ R := by simpa using hiR
    have hiS' : i ∈ S := by simpa using hiS
    exact (Finset.disjoint_left.mp hDis) hiS' hiR'
  apply (List.perm_ext_iff_of_nodup _ _).mpr
  · intro i
    simp
  · exact (R.sort_nodup (· ≤ ·)).append (S.sort_nodup (· ≤ ·)) hdis
  · exact (R ∪ S).sort_nodup (· ≤ ·)

/-- The same tower transforms the globally sorted complete window by a
permutation of the actual residual-first head boundary, including born slots. -/
theorem residual_containing_sorted_union_transform_perm {n : ℕ} {X Y : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (D : ι → Set X) (R S : Finset ι) (hDis : Disjoint S R)
    (J : GermIdeal n X) (T : BlowupTower X Y) :
    (geoTransformAlong (fullMarked ((R.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D) J) T).E.Perm
      (geoTransformAlong (fullMarked (((R ∪ S).sort (· ≤ ·)).map D) J) T).E := by
  apply perm_geoTransformAlong_boundary
  simpa only [fullMarked,List.map_append] using (residual_containing_sorted_union_perm R S hDis).map D
end
end Hironaka.HironakaG3CanonicalWindowPermutation
