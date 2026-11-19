import Hironaka.Resolution.HironakaG34ToricCharts

/-!
# Uniform source neighborhoods for near-identity coordinate scalings

A scaling's source is an open depending on the parameter. These lemmas find
one product-neighborhood in which every point belongs to its appropriate
source, including after pullback along a continuous projection.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG4UniformScalingDomain
noncomputable section
open BlowupFlatCoordinates HironakaG34CoordinateScaling
  HironakaNormalCrossingsDiagonalLiftOrbits HironakaG34ToricCharts

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {x₀ : X}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
  (O : Opens (ComplexModel n)) {x : X}

/-- Near `(1,x)`, the variable scaling domain contains the variable point. -/
theorem eventually_mem_scaleDomain (hx : x ∈ flatDomain Φ) (hxO : flatMap Φ x ∈ O) :
    ∀ᶠ p : (Fin n → ℂ) × X in 𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 x,
      p.2 ∈ scaleDomain Φ O p.1 := by
  have hflat : Tendsto (flatMap Φ) (𝓝 x) (𝓝 (flatMap Φ x)) :=
    ((continuousOn_flatMap Φ).continuousAt ((isOpen_flatDomain Φ).mem_nhds hx)).tendsto
  have hscale : Tendsto (fun p : (Fin n → ℂ) × X => diagonal p.1 (flatMap Φ p.2))
      (𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 x) (𝓝 (flatMap Φ x)) := by
    have h := (continuous_diagonal_prod.tendsto (1, flatMap Φ x)).comp
      (tendsto_fst.prodMk_nhds (hflat.comp tendsto_snd))
    rwa [diagonal_one] at h
  filter_upwards [tendsto_snd.eventually ((isOpen_flatDomain Φ).mem_nhds hx),
    tendsto_snd.eventually (hflat.eventually (O.isOpen.mem_nhds hxO)),
    hscale.eventually (O.isOpen.mem_nhds hxO)] with p hp hO hpO
  exact ⟨hp, hO, hpO⟩

/-- The same common source works over the terminal stage of a tower, or any
continuous projection. -/
theorem eventually_preimage_mem_scaleDomain {Y : Type*} [TopologicalSpace Y]
    (q : Y → X) {y : Y} (hq : ContinuousAt q y)
    (hx : q y ∈ flatDomain Φ) (hxO : flatMap Φ (q y) ∈ O) :
    ∀ᶠ p : (Fin n → ℂ) × Y in 𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 y,
      q p.2 ∈ scaleDomain Φ O p.1 := by
  have hp : Tendsto (fun p : (Fin n → ℂ) × Y => (p.1, q p.2))
      (𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 y) (𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 (q y)) :=
    tendsto_fst.prodMk (hq.tendsto.comp tendsto_snd)
  exact hp.eventually (eventually_mem_scaleDomain Φ O hx hxO)

end
end Hironaka.HironakaG4UniformScalingDomain
