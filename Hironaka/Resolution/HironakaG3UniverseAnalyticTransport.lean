import Hironaka.Resolution.HironakaG3UniverseComplexTransport
import Hironaka.Analytic.AnalyticSubsetPreimage
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseAnalyticTransport
noncomputable section
open HironakaG3UniverseChartTransport AnalyticSubsetPreimage

/-- Analytic subsets are preserved in both directions by the transported complex atlas. -/
theorem transported_analytic_iff {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) (A : Set X) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsComplexAnalyticSubset (n := n) (e.symm ⁻¹' A) ↔ IsComplexAnalyticSubset (n := n) A := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  constructor
  · intro h
    have hh := isComplexAnalyticSubset_preimage (transported_homeomorph_contMDiff e) h
    have heq : e ⁻¹' (e.symm ⁻¹' A) = A := by ext x; simp
    rw [heq] at hh
    exact hh
  · exact isComplexAnalyticSubset_preimage (transported_homeomorph_symm_contMDiff e)
end
end Hironaka.HironakaG3UniverseAnalyticTransport
