import Hironaka.Resolution.HironakaG3LocallyFiniteDisjointUnionNC
import Hironaka.Resolution.HironakaG3IndexedTopContactEndpoint
import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StrictComponentUnionBoundary
universe u v
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG3IndexedSeparatedComponents
  HironakaG3LocallyFiniteDisjointUnionNC HironakaG3IndexedTopContactEndpoint

theorem strict_component_union_boundary {n : ℕ} {X Z : CMfd.{0} n} {ι : Type u} {κ : Type v}
    (C : ι → Set X) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (D : κ → Set Z) (hD : IsLocallyFiniteSNCDivisor n D)
    (hNC : ∀ i, HasNormalCrossingsWithBoundary (strictTransform n P (C i)) D) :
    ∃ (ρ : Type v) (B : ρ → Set Z), IsLocallyFiniteSNCDivisor n B ∧
      (∀ a, (B a).Nonempty) ∧ (⋃ a, B a) = ⋃ a, D a ∧
      HasNormalCrossingsWithBoundary (⋃ i, strictTransform n P (C i)) B := by
  let T : ι → Set Z := fun i => strictTransform n P (C i)
  have hTclosed : ∀ i, IsClosed (T i) := fun _ => isClosed_closure
  have hTLF : LocallyFinite T := locallyFinite_strictTransforms C hClosed hLF hP.continuous
  have hTdis : ∀ i j, i ≠ j → Disjoint (T i) (T j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    have hi' := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hClosed i) hi
    have hj' := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hClosed j) hj
    exact Set.disjoint_left.mp (hDis i j hij) hi' hj'
  have hUnionNC : HasNormalCrossingsWithBoundary (⋃ i, T i) D :=
    locally_finite_disjoint_union_nc T D hTclosed hTLF hTdis hNC
  exact nonempty_boundary_reindex D hD hUnionNC
end
end Hironaka.HironakaG3StrictComponentUnionBoundary
