import Hironaka.Resolution.HironakaG34ToricCharts

/-!
# Partial character realization suffices for centres inside a coordinate carrier

The source route's weighted torus has full rank only on coordinates outside
the carrier's normal mask. A centre contained in that carrier has zero values
on the remaining coordinates. Therefore the actual preserving action and a
section realizing only the free characters imply the full scaling-invariance
hypothesis of the existing chart torus lemma.

This is a single-chart implication from primitive actual action data, not an
assumption of all-future charts or equivariant protection. The native history
must still construct these data and the section at each actual stage.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4PartialToricRealization

noncomputable section

open BlowupFlatCoordinates NormalCrossings HironakaG34CoordinateScaling
  HironakaG34ToricCharts HironakaNormalCrossingsDiagonalLiftOrbits

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- Realizing only the coordinates outside the carrier's zero mask suffices
to derive full coordinate-scaling invariance of a preserved centre germ. -/
theorem scaling_invariant_of_partial_realization
    {A : Type*} {F : Filter A} {act : A → M → M} {μ : A → Fin n → ℂ}
    {C : Set M} (S₀ : Finset (Fin n))
    (hdiag : ActsDiagonallyNear F act μ Φ x)
    (hpreserve : ∀ᶠ p : A × M in F ×ˢ 𝓝 x, p.2 ∈ C → act p.1 p.2 ∈ C)
    (hzero : ∀ᶠ q in 𝓝 x, q ∈ C → ∀ i ∈ S₀, flatMap Φ q i = 0)
    (s : (Fin n → ℂ) → A) (hs : Tendsto s (𝓝 1) F)
    (hrealize : ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S₀, μ (s τ) i = τ i) :
    ∀ᶠ q in 𝓝 x, q ∈ C → ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ),
      ∀ q' ∈ flatDomain Φ, flatMap Φ q' = diagonal τ (flatMap Φ q) → q' ∈ C := by
  obtain ⟨P, hP, U, hU, hPU⟩ := mem_prod_iff.mp (hdiag.and hpreserve)
  filter_upwards [hU, hzero] with q hq hqzero hqC
  filter_upwards [hs.eventually hP, hrealize] with τ hτ hτreal q' hq' hq'eq
  have hdata := hPU (show (s τ, q) ∈ P ×ˢ U from ⟨hτ, hq⟩)
  have hscales : diagonal (μ (s τ)) (flatMap Φ q) = diagonal τ (flatMap Φ q) := by
    ext i
    simp only [diagonal_apply]
    by_cases hi : i ∈ S₀
    · rw [hqzero hqC i hi]
      simp
    · rw [hτreal i hi]
  have hcoords : flatMap Φ (act (s τ) q) = flatMap Φ q' :=
    hdata.1.2.2.trans (hscales.trans hq'eq.symm)
  have hpoints : act (s τ) q = q' := by
    calc
      act (s τ) q = (chartAt (ComplexModel n) x).symm
          (Φ.invFun (flatMap Φ (act (s τ) q))) :=
        (flatInverse_flat Φ hdata.1.2.1).symm
      _ = (chartAt (ComplexModel n) x).symm (Φ.invFun (flatMap Φ q')) := by rw [hcoords]
      _ = q' := flatInverse_flat Φ hq'
  rw [← hpoints]
  exact hdata.2 hqC

end

end Hironaka.HironakaG4PartialToricRealization
