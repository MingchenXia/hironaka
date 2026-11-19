import Hironaka.Resolution.HironakaG4RebaseFlatChart
import Hironaka.Resolution.HironakaG34ToricCharts

/-!
# Rebasing an uncentred diagonal chart

The rebased chart retains literal old coordinates. Joint convergence of the
actual action follows from the old diagonal equation and lets its diagonal
relation be restricted to the new chart.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4RebaseDiagonalAction
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates HironakaG34CoordinateScaling
  HironakaG34ToricCharts HironakaNormalCrossingsDiagonalLiftOrbits HironakaG4RebaseFlatChart

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {x₀ x : X}

/-- An actual diagonal action converges jointly at every point where its
local diagonal equation holds and the character tends to the identity. -/
theorem tendsto_action_of_diagonal_at_domain_point
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hx : x ∈ flatDomain (y₀ := x₀) Φ)
    {A : Type*} {F : Filter A} {act : A → X → X} {μ : A → Fin n → ℂ}
    (hμ : Tendsto μ F (𝓝 1)) (hdiag : ActsDiagonallyNear F act μ Φ x) :
    Tendsto (fun p : A × X => act p.1 p.2) (F ×ˢ 𝓝 x) (𝓝 x) := by
  have hflat := ((continuousOn_flatMap Φ).continuousAt ((isOpen_flatDomain Φ).mem_nhds hx)).tendsto
  have hcoord : Tendsto (fun p : A × X => diagonal (μ p.1) (flatMap Φ p.2))
      (F ×ˢ 𝓝 x) (𝓝 (flatMap Φ x)) := by
    have h := (continuous_diagonal_prod.tendsto (1, flatMap Φ x)).comp
      ((hμ.comp tendsto_fst).prodMk_nhds (hflat.comp tendsto_snd))
    rwa [diagonal_one] at h
  have hinv := (tendsto_flatInverse Φ hx).comp hcoord
  apply hinv.congr'
  filter_upwards [hdiag] with p hp
  change (chartAt (ComplexModel n) x₀).symm
    (Φ.invFun (diagonal (μ p.1) (flatMap Φ p.2))) = act p.1 p.2
  rw [← hp.2.2]
  exact flatInverse_flat Φ hp.2.1

/-- Rebase the chart at a domain point while retaining its exact coordinates
and the actual diagonal action. -/
theorem exists_rebased_diagonal_chart
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hx : x ∈ flatDomain (y₀ := x₀) Φ)
    {A : Type*} {F : Filter A} {act : A → X → X} {μ : A → Fin n → ℂ}
    (hμ : Tendsto μ F (𝓝 1)) (hdiag : ActsDiagonallyNear F act μ Φ x) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      (∀ y ∈ flatDomain (y₀ := x) Ψ, y ∈ flatDomain (y₀ := x₀) Φ ∧
        flatMap (x₀ := x) Ψ y = flatMap (x₀ := x₀) Φ y) ∧
      ActsDiagonallyNear F act μ Ψ x := by
  obtain ⟨Ψ, hΨsrc, hcoords⟩ := exists_rebased_flat_chart Φ hx
  have hact := tendsto_action_of_diagonal_at_domain_point Φ hx hμ hdiag
  have hsource : ∀ᶠ p in F ×ˢ 𝓝 x, p.2 ∈ flatDomain Ψ :=
    tendsto_snd.eventually ((isOpen_flatDomain Ψ).mem_nhds (mem_flatDomain_self Ψ))
  have htarget : ∀ᶠ p in F ×ˢ 𝓝 x, act p.1 p.2 ∈ flatDomain Ψ :=
    hact.eventually ((isOpen_flatDomain Ψ).mem_nhds (mem_flatDomain_self Ψ))
  refine ⟨Ψ, hΨsrc, hcoords, ?_⟩
  filter_upwards [hsource, htarget, hdiag] with p hp hp' hd
  refine ⟨hp, hp', ?_⟩
  rw [(hcoords _ hp').2, hd.2.2, ← (hcoords _ hp).2]

end
end Hironaka.HironakaG4RebaseDiagonalAction
