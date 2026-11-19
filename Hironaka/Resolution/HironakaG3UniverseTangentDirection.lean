import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseTangentDirection
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong
  DerivativeIdealAlongEtale DerivativeIdealAlongCoherent GiraudAlong TangentDirectionAlong
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u : M → ℂ}

theorem isTangentDirectionAlong_pullback {M' : Type v} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
    [IsComplexManifold n M'] {φ : M' → M} (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {V : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ V u) :
    IsTangentDirectionAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) μ (φ ⁻¹' V) (u ∘ φ) where
  isOpen := by
    have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun y =>
      (hloc y).choose_spec.mdiff.self_of_nhds.continuousAt
    exact hu.isOpen.preimage hφc
  mem y hy := by
    obtain ⟨ψ, h⟩ := hloc y
    rw [← pullback_iterDerivIdealAlong hloc h𝔞 (μ - 1)]
    exact comp_mem_pullback h.mdiff (hu.mem (φ y) hy)
      (holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) (φ y) u (hu.mem (φ y) hy))
  multiplicity_one y hy hy0 := by
    obtain ⟨ψ, h⟩ := hloc y
    obtain ⟨e, ξ, hξ, hne⟩ := hu.multiplicity_one (φ y) hy hy0
    have hy' : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
    have huhol : HolomorphicAt n u (φ y) :=
      holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) (φ y) u (hu.mem (φ y) hy)
    have hghol : HolomorphicAt n (u ∘ φ) y := HadamardBridge.holomorphicAt_comp_map h.mdiff huhol
    refine ⟨complexChartAt (n := n) y, transferField φ ψ e (complexChartAt (n := n) y) ξ,
      isTangentField_transfer h hy' hξ, ?_⟩
    have hcongr := fieldDeriv_transfer h hy' hξ.mem_source ξ hghol
    rw [hcongr.self_of_nhds]
    have hloc' : ((u ∘ φ) ∘ ψ) =ᶠ[𝓝 (φ y)] u := by
      filter_upwards [h.right_inv] with q hq
      simp only [Function.comp_apply, hq]
    show fieldDeriv e ξ ((u ∘ φ) ∘ ψ) (φ y) ≠ 0
    rw [(fieldDeriv_congr hξ.mem_source hloc').self_of_nhds]
    exact hne

end
end Hironaka.G3UniverseTangentDirection
