/- Complete original prerequisite; statement and mathematical proof unchanged. -/
import Hironaka.MarkedIdeal.NormalDerivativeChart

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace Hironaka.NormalDerivativeChart

open Hironaka.HolomorphicIdealSheaves HolomorphicTaylorTail GermIdealOrder IdealWeightPowers
  NormalTaylorOrder DerivativeIdeal BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace FlatChart

variable {S : Set M} {p : M} {k : ℕ} (c : FlatChart n S p k)

/-- The empty normal derivative is the function itself near `p`. -/
theorem nd_nil (f : M → ℂ) : c.nd [] f =ᶠ[𝓝 p] f := by
  filter_upwards [c.eventually_inv_ψ] with y hy
  simp only [nd, List.map_nil, iterDeriv_nil, hy]

/-- **Derivatives in a flat chart of a germ of `𝔟` lie in `𝓓^{|L|}(𝔟)`** (coherent `𝔟`): every coordinate derivative
is a holomorphic combination of chart derivatives. -/
theorem nd_mem_iterDerivIdeal {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {g : M → ℂ} (hg : 𝔟.mem p g) :
    ∀ L : List (Fin n), (iterDerivIdeal 𝔟 L.length).mem p (c.nd L g)
  | [] => mem_congr_of_isCoherent h𝔟 hg (c.nd_nil g).symm
  | l :: L => by
    have hhol : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
    set e := complexChartAt (n := n) p with he
    have hes : e.val = chartAt (ComplexModel n) p := rfl
    have hps : p ∈ e.val.source := mem_complexChartAt_source p
    -- the chart reading of `ψ` is `Φ` near `e p`
    set Nset : Set (ComplexModel n) := e.val.target ∩ c.Φ.source with hNset
    have hNo : IsOpen Nset := e.val.open_target.inter c.Φ.isOpen_source
    have hpN : e.val p ∈ Nset := ⟨e.val.map_source hps, c.Φ.center_mem_source⟩
    have hFeq : ∀ ζ ∈ Nset, (c.ψ ∘ e.val.symm) ζ = c.Φ.toFun ζ := fun ζ hζ => by
      simp only [Function.comp_apply, ψ, ← hes, e.val.right_inv hζ.1]
    have hFd : DifferentiableOn ℂ (c.ψ ∘ e.val.symm) Nset := fun ζ hζ =>
      ((c.Φ.toFun_holomorphic.differentiableAt (c.Φ.isOpen_source.mem_nhds hζ.2)).congr_of_eventuallyEq
        (eventually_of_mem (hNo.mem_nhds hζ) fun ζ' hζ' => hFeq ζ' hζ')).differentiableWithinAt
    have hinj : Function.Injective (fderiv ℂ (c.ψ ∘ e.val.symm) (e.val p)) := by
      have hloc : (c.ψ ∘ e.val.symm) =ᶠ[𝓝 (e.val p)] c.Φ.toFun :=
        eventually_of_mem (hNo.mem_nhds hpN) fun ζ' hζ' => hFeq ζ' hζ'
      rw [hloc.fderiv_eq]
      exact c.injective_fderiv_Φ c.Φ.center_mem_source
    obtain ⟨cf, hcf, hceq⟩ := BlowupDerivativeIdeal.exists_coordDeriv_coeff hNo hpN hFd hinj
    have hprev := nd_mem_iterDerivIdeal h𝔟 hg L
    -- `G = ∂^L (g ∘ inv)` is holomorphic near `ψ p = 0`
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (c.eventually_differentiableAt_comp_inv (hhol p g hg))
    have hGU : DifferentiableOn ℂ (fun u => g (c.inv u)) (ball 0 r) := fun z hz =>
      (hball z hz).differentiableWithinAt
    have hdj := differentiableOn_iterDeriv hGU isOpen_ball (L.map bv)
    have hGev : ∀ᶠ w in 𝓝 (c.ψ p), DifferentiableAt ℂ (iterDeriv (L.map bv) (fun u => g (c.inv u))) w := by
      rw [c.ψ_self]
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
      exact (hdj w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have heq := hceq _ hGev l
    have hmem : (iterDerivIdeal 𝔟 (L.length + 1)).mem p (fun y => ∑ m, cf l m y *
        chartDeriv e (EuclideanSpace.single m 1) (iterDeriv (L.map bv) (fun u => g (c.inv u)) ∘ c.ψ) y) := by
      refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun m _ => ?_
      exact RelativePrincipalizationSpan.IsInSpanAt.mul_left (hcf l m)
        (chartDeriv_mem_derivIdeal (holomorphicAt_of_mem_iterDerivIdeal hhol L.length) hps hprev)
    refine DerivativeIdeal.isInSpanAt_congr hmem ?_
    filter_upwards [heq] with y hy
    simp only [nd, List.map_cons, iterDeriv_cons, dirDeriv]
    exact hy.symm

end FlatChart

end

end Hironaka.NormalDerivativeChart

