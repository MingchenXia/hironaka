import Hironaka.Resolution.HironakaG3UniverseRegularTransport
import Hironaka.Resolution.HironakaG3UniverseAnalyticTransport
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff Topology
universe u v
namespace Hironaka.HironakaG3UniversePureTransport
noncomputable section
open HironakaG3UniverseChartTransport HironakaG3UniverseCoordinateTransport
  HironakaG3UniverseAnalyticTransport

/-- The regular locus is transported by the same homeomorphism. -/
theorem transported_regularLocus {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) (A : Set X) (d : ℕ) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    regularLocus (n := n) (e.symm ⁻¹' A) d = e.symm ⁻¹' regularLocus (n := n) A d := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  ext y
  exact transported_regularAtDim_iff e A y d

/-- Pure analytic input transports to the literal transported subset. -/
theorem transported_pure_analytic {n d : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) (A : Set X)
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hPure : A ⊆ closure (regularLocus (n := n) A d)) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsComplexAnalyticSubset (n := n) (e.symm ⁻¹' A) ∧
      e.symm ⁻¹' A ⊆ closure (regularLocus (n := n) (e.symm ⁻¹' A) d) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  refine ⟨(transported_analytic_iff e A).2 hA, ?_⟩
  rw [transported_regularLocus, ← e.symm.preimage_closure]
  exact preimage_mono hPure
end
end Hironaka.HironakaG3UniversePureTransport
