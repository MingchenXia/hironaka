import Hironaka.Resolution.HironakaG3SeparatorIrreducible
import Hironaka.Resolution.HironakaG3IndexedBoundaryDichotomy
import Hironaka.Resolution.HironakaG3IndexedCanonicalContact
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatorBoundaryDichotomy
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3IndexedMixedGluing HironakaG3IndexedMixedBad
  HironakaG3ProperDenseIrreducible HironakaG3IndexedBoundaryDichotomy
  HironakaG3IndexedCanonicalContact HironakaActualLocallyFiniteBoundary
  HironakaG3IndexedSeparatedComponents HironakaActualIndexedBoundaryContinuation

/-- Each actual separated strict component is either contained in an indexed
boundary member or dense away from the full locally finite boundary. -/
theorem separator_component_boundary_dichotomy {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ τ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P)
    (E : τ → Set Z) (hE : IsLocallyFiniteSNCDivisor n E) (a : ι) :
    (∃ i, strictTransform n P (V a).carrier ⊆ E i) ∨
      strictTransform n P (V a).carrier ⊆
        closure (strictTransform n P (V a).carrier \ ⋃ i, E i) := by
  let : LinearOrder τ := WellOrderingRel.isWellOrder.linearOrder
  exact irreducible_locally_finite_boundary_dichotomy
    (indexed_separator_strictTransform_irreducible V hDim hDistinct D h a)
    E hE.1 (isComplexAnalyticSubset_member E hE)

/-- The actual separated strict component is a closed irreducible analytic
subvariety with exactly its original dimension. -/
theorem exists_separator_strict_component {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) (a : ι) :
    ∃ W : ClosedIrreducibleAnalyticSubvariety n Z,
      W.carrier = strictTransform n P (V a).carrier ∧ W.dim = (V a).dim := by
  let A := strictTransform n P (V a).carrier
  have hI : IsComplexAnalyticallyIrreducible (n := n) A :=
    indexed_separator_strictTransform_irreducible V hDim hDistinct D h a
  have hpure : A ⊆ closure (regularLocus (n := n) A (V a).dim) :=
    strictTransform_subset_closure_regularLocus h.1 (V a).isClosed_carrier
      (HironakaEmbeddedReducible.subset_closure_regularLocus (V a))
  have hreg : (regularLocus (n := n) A (V a).dim).Nonempty := by
    obtain ⟨z,hz⟩ := hI.nonempty
    by_contra hnone
    have hclose := hpure hz
    rw [not_nonempty_iff_eq_empty.mp hnone,closure_empty] at hclose
    exact hclose
  exact ⟨⟨A,hI.analytic.isClosed,hI,(V a).dim,(V a).dim_le,hreg⟩,rfl,rfl⟩

/-- For each separated component, the actual containing-label intersection
is smooth and the component is dense off the residual indexed boundary. -/
theorem separator_component_canonical_contact {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ τ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P)
    (E : τ → Set Z) (hE : IsLocallyFiniteSNCDivisor n E) (a : ι) :
    let C := strictTransform n P (V a).carrier
    let hC := indexed_separator_strictTransform_irreducible V hDim hDistinct D h a
    let S := HironakaG3IndexedContainingBoundary.containingLabels C E hC.nonempty hE.1
    let N := canonicalContact C E hC.nonempty hE.1
    C ⊆ N ∧ N.Nonempty ∧ IsClosed N ∧
      (∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card)) ∧
      S.card ≤ n ∧ IsClosedSubmanifold n N ∧
      C ⊆ closure (C \ ⋃ i : {i // i ∉ S}, E i.val) := by
  let : LinearOrder τ := WellOrderingRel.isWellOrder.linearOrder
  let C := strictTransform n P (V a).carrier
  let hC := indexed_separator_strictTransform_irreducible V hDim hDistinct D h a
  have hGeom := canonicalContact_geometry C E hC hE
  have hDense := dense_off_residual_family C E hC hE
  exact ⟨hGeom.1,hGeom.2.1,hGeom.2.2.1,hGeom.2.2.2.1,hGeom.2.2.2.2.1,hGeom.2.2.2.2.2,hDense⟩
end
end Hironaka.HironakaG3SeparatorBoundaryDichotomy
