import Hironaka.Resolution.HironakaG3UniversePureTransport
import Hironaka.Resolution.HironakaG3UniverseIndexedSNC
import Hironaka.Resolution.HironakaG3UniverseSmallBoundaryReindex
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff Topology
universe u v w
namespace Hironaka.HironakaG3UniversePureBoundaryInput
noncomputable section
open BlowupTowers HironakaActualLocallyFiniteBoundary HironakaG3UniverseChartTransport
  HironakaG3UniversePureTransport HironakaG3UniverseIndexedSNC HironakaG3UniverseSmallBoundaryReindex

/-- Actual pure target and a same-support small indexed boundary on the transported manifold. -/
theorem transported_pure_boundary_input_with_labels {n d : ℕ} (X : CMfd.{u} n) {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) (A : Set X)
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hPure : A ⊆ closure (regularLocus (n := n) A d)) {ι : Type w}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsComplexAnalyticSubset (n := n) (e.symm ⁻¹' A) ∧
      e.symm ⁻¹' A ⊆ closure (regularLocus (n := n) (e.symm ⁻¹' A) d) ∧
      ∃ (κ : Type) (f : κ → ι),
        Injective f ∧ (∀ i, (D i).Nonempty → i ∈ range f) ∧
        let B : κ → Set Y := fun j => e.symm ⁻¹' D (f j)
        IsLocallyFiniteSNCDivisor n (Q := CMfd.of (n := n) Y) B ∧
        (∀ j, (B j).Nonempty) ∧ (⋃ j, B j) = e.symm ⁻¹' (⋃ i, D i) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  obtain ⟨hA',hPure'⟩ := transported_pure_analytic e A hA hPure
  obtain ⟨κ,f,hf,hRange,hC,hNE,hUnion⟩ := exists_small_boundary_reindex_with_labels X D hD
  let C : κ → Set X := fun j => D (f j)
  refine ⟨hA',hPure',κ,f,hf,hRange,transported_indexed_snc X e C hC,?_,?_⟩
  · intro j
    obtain ⟨x,hx⟩ := hNE j
    exact ⟨e x,by simpa using hx⟩
  · ext y
    simp only [mem_iUnion,mem_preimage] at *
    have hh := Set.ext_iff.mp hUnion (e.symm y)
    simpa only [mem_iUnion] using hh

theorem transported_pure_boundary_input {n d : ℕ} (X : CMfd.{u} n) {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) (A : Set X)
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hPure : A ⊆ closure (regularLocus (n := n) A d)) {ι : Type w}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsComplexAnalyticSubset (n := n) (e.symm ⁻¹' A) ∧
      e.symm ⁻¹' A ⊆ closure (regularLocus (n := n) (e.symm ⁻¹' A) d) ∧
      ∃ (κ : Type) (B : κ → Set Y),
        IsLocallyFiniteSNCDivisor n (Q := CMfd.of (n := n) Y) B ∧
        (∀ j, (B j).Nonempty) ∧ (⋃ j, B j) = e.symm ⁻¹' (⋃ i, D i) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  obtain ⟨hA',hPure',κ,f,_hf,_hRange,hD',hNE,hUnion⟩ := transported_pure_boundary_input_with_labels X e A hA hPure D hD
  exact ⟨hA',hPure',κ,fun j => e.symm ⁻¹' D (f j),hD',hNE,hUnion⟩

end
end Hironaka.HironakaG3UniversePureBoundaryInput
