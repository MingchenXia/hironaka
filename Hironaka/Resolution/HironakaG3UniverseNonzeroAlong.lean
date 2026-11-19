import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseNonzeroAlong
open Hironaka.HolomorphicIdealSheaves DivisorExponentAlong
  RelativePrincipalizationSpan HadamardBridge
noncomputable section

/-- A holomorphic homeomorphism preserves a nonzero restricted germ under pullback. -/
theorem nonzeroAlong_pullback_homeomorph {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₜ X) (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    {N : Set X} {I : GermIdeal n X} (hI : I.IsCoherent) {y : Y}
    (hne : IsNonzeroAlongAt N I (e y)) :
    IsNonzeroAlongAt (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) y := by
  obtain ⟨g,hg,hfreq⟩ := hne
  refine ⟨g ∘ e,?_,?_⟩
  · have hfh : ∀ᶠ w in 𝓝 y, MDifferentiableAt
        𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e w :=
      Eventually.of_forall fun w => (he w).mdifferentiableAt (by simp)
    exact GermIdeal.mem_pullback_iff.mpr <| isInSpanAt_of_eq_mul ⟨g,hg,rfl⟩
      (holomorphicAt_comp_map hfh (GermIdeal.IsCoherent.holomorphicAt_mem hI hg)) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)
  · rw [← e.map_nhds_eq,Filter.frequently_map] at hfreq
    exact hfreq
end
end Hironaka.HironakaG3UniverseNonzeroAlong
