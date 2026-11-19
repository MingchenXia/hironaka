import Hironaka.Resolution.HironakaG3BoundaryDenseOffComponents
import Hironaka.Resolution.HironakaG3SeparatorIrreducible
set_option autoImplicit false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3InheritedBornNoCollision
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3BoundaryDenseOffComponents HironakaG3ProperDenseIrreducible

/-- Every actual inherited strict transform is dense away from the preimage
of the whole zero-containing component union. -/
theorem inherited_strict_dense_off_component_preimage {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P) (j : κ) :
    strictTransform n P (D j) ⊆ closure (strictTransform n P (D j) ∩ P ⁻¹' (⋃ i, C i)ᶜ) := by
  apply strictTransform_dense_over_dense_subset hP (hD.2.1 j)
  simpa only [sdiff_eq] using indexed_boundary_dense_off_zero_containing_components C r D hC hLF hD hS hr hpure j

/-- No nonempty open-chart trace of an inherited strict member can be
contained in a set supported over the component union. -/
theorem inherited_trace_not_supported_over_components {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (j : κ) (O : Opens Z) (hNE : (strictTransform n P (D j) ∩ O).Nonempty)
    (B : Set Z) (hB : B ⊆ P ⁻¹' (⋃ i, C i)) :
    ¬ strictTransform n P (D j) ∩ O ⊆ B := by
  obtain ⟨x,hxD,hxO⟩ := hNE
  have hxcl := inherited_strict_dense_off_component_preimage C r D hC hLF hD hS hr hpure hP j hxD
  obtain ⟨y,hyO,hyD,hyOut⟩ := mem_closure_iff_nhds.mp hxcl O (O.isOpen.mem_nhds hxO)
  intro hSub
  exact hyOut (hB (hSub ⟨hyD,hyO⟩))
end
end Hironaka.HironakaG3InheritedBornNoCollision
