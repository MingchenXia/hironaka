import Hironaka.Resolution.HironakaG3SortedLocalWindowGeometry
import Hironaka.Resolution.HironakaG3TopContactBiholoEmptyClass
import Hironaka.Resolution.HironakaActualIndexedBoundaryContinuation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3TopReflSortedWindowGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass
  HironakaG3TopContactBiholoEmptyClass HironakaG3SortedLocalWindowGeometry
  HironakaG3OrderedFiniteWindows HironakaDisjointFiniteControlledHistory

/-- The genuine top-contact empty class restricted to actual zero-length towers. -/
def topReflClass {n : ℕ} {X : CMfd.{0} n} : LocalTowerClass X :=
  fun U Y T => biholoEmptyClass U Y T ∧ T.length = 0

theorem top_refl_class_comparisons {n : ℕ} {X : CMfd.{0} n} : HasComparisons (topReflClass (X := X)) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  exact biholo_empty_class_comparisons U₁ U₂ Y₁ Y₂ T₁ T₂ h₁.1 h₂.1

theorem top_refl_class_member {n : ℕ} {X : CMfd.{0} n} (U : Opens X) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), topReflClass U Y T := by
  exact ⟨CMfd.of (n := n) U,.refl,⟨trivial,Diffeomorph.refl _ _ ∞,fun _ => rfl⟩,rfl⟩

theorem top_refl_sorted_local_window_geometry {n : ℕ} {X : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hClosed : IsClosed C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hNC : HasNormalCrossingsWithBoundary C D) : HasSortedLocalWindowGeometry C D topReflClass := by
  intro U Y T hT R hR
  refine ⟨R,hR,?_⟩
  have hLen := hT.2
  cases T with
  | refl =>
    let l := R.sort (· ≤ ·)
    let B := l.map D
    let e : Fin l.length ↪ κ := ⟨l.get,(R.sort_nodup (· ≤ ·)).injective_get⟩
    have hB : IsSNCDivisor n B := sorted_boundary_snc D hD R
    have hBC : HasNormalCrossings n C B := by
      have hh := hasNormalCrossings_finiteBoundary C D hNC e
      have heq : (List.ofFn fun i : Fin l.length => D (l.get i)) = B := by
        simpa only [List.get_eq_getElem, B] using List.ofFn_getElem_eq_map l D
      change HasNormalCrossings n C (List.ofFn fun i : Fin l.length => D (l.get i)) at hh
      rw [heq] at hh
      exact hh
    have hBU := NormalCrossingsInvariance.isSNCDivisor_map_preimage (pullsBackCoordinates_val U)
      continuous_subtype_val hB
    have hBCU := NormalCrossingsInvariance.hasNormalCrossings_preimage (pullsBackCoordinates_val U) hBC
    have hC : IsClosed ((Subtype.val : U → X) ⁻¹' C) := hClosed.preimage continuous_subtype_val
    have hST : strictTransform n (id : U → U) ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C := by
      simp [strictTransform,exceptionalLocus_id]
    simpa [geoTransformAlong_refl,fullMarked,hST,B,l] using And.intro hBU hBCU
  | @step Y Z T C₀ π hπ =>
    simp at hLen
end
end Hironaka.HironakaG3TopReflSortedWindowGeometry
