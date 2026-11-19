import Hironaka.Resolution.HironakaG3DisjointActiveFootprint
import Hironaka.Resolution.HironakaG3SeparatorIrreducible
import Hironaka.Resolution.HironakaG3InheritedLabelsDistinct
set_option autoImplicit false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingActiveInheritedLabels
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3DisjointActiveFootprint HironakaG3ProperDenseIrreducible HironakaG3InheritedLabelsDistinct

variable {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hLF : LocallyFinite C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))

/-- The active supports are exactly those selected for nontrivial contact classes. -/
def varyingActiveUnion : Set X := ⋃ i : {i // (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
    r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card}, C i.val

include hLF hr hpure

theorem varying_inherited_dense_off_active {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P) (j : κ) :
    strictTransform n P (D j) ⊆ closure (strictTransform n P (D j) ∩ P ⁻¹' (varyingActiveUnion C r D hC hD)ᶜ) := by
  apply strictTransform_dense_over_dense_subset hP (hD.2.1 j)
  simpa only [varyingActiveUnion,sdiff_eq] using
    indexed_boundary_dense_off_varying_active_components C r D hC hLF hD hr hpure j

theorem varying_inherited_trace_not_active_supported {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (j : κ) (O : Opens Z) (hNE : (strictTransform n P (D j) ∩ O).Nonempty)
    (B : Set Z) (hB : B ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD)) :
    ¬ strictTransform n P (D j) ∩ O ⊆ B := by
  obtain ⟨x,hxD,hxO⟩ := hNE
  have hxcl := varying_inherited_dense_off_active C r D hC hLF hD hr hpure hP j hxD
  obtain ⟨y,hyO,hyD,hyOut⟩ := mem_closure_iff_nhds.mp hxcl O (O.isOpen.mem_nhds hxO)
  intro hSub
  exact hyOut (hB (hSub ⟨hyD,hyO⟩))

theorem varying_inherited_trace_labels_eq {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (hExc : exceptionalLocus n P ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD))
    (j k : κ) (O : Opens Z) (hNE : (strictTransform n P (D j) ∩ O).Nonempty)
    (hEq : strictTransform n P (D j) ∩ O = strictTransform n P (D k) ∩ O) : j = k := by
  have hF : IsClosed (varyingActiveUnion C r D hC hD) := by
    unfold varyingActiveUnion
    exact (hLF.comp_injective Subtype.val_injective).isClosed_iUnion (fun i => (hC i.val).analytic.isClosed)
  exact inherited_trace_labels_eq_of_density_footprint D hD _ hF hP hExc j k
    (varying_inherited_dense_off_active C r D hC hLF hD hr hpure hP j) O hNE hEq
end
end Hironaka.HironakaG3VaryingActiveInheritedLabels
