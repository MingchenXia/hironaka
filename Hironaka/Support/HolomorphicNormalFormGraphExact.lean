/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.HolomorphicConstantRank
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false

/-!
# The constant rank theorem for holomorphic maps

Blueprint `rem:constant-rank` (used without proof in Demailly, *Complex analytic and differential
geometry*, II.8.1 and II.8.5).  Let `G : E → F` be holomorphic on an open set `U` of a
finite-dimensional complex normed space, with `rank dG_z = r` for every `z ∈ U`, and `p ∈ U`.
Write `L = dG_p`, `R = range L` (dimension `r`) and `K = ker L`.

* `exists_normalForm`: there are continuous linear projections `Q : F → R` and `S : E → K`, a
  ball `B` around `Ψ p` in `R × K`, where `Ψ z = (Q (G z), S z)`, a holomorphic inverse `ψ : B → U`
  of `Ψ` (`Ψ (ψ w) = w`, `ψ (Ψ p) = p`, `ψ '' B` open), and a holomorphic `k` on the first factor
  of `B` with `Q ∘ k = id` and the normal form
  `G (ψ w) = k w.1`  for `w ∈ B`:
  in the chart `ψ`, `G` depends only on the first `r` coordinates and is the graph map `k` there.
* `exists_ne_mem_fibre`: if `r < dim E`, then `p` is an accumulation point of its fibre
  `G⁻¹(G p)`.
* `image_eq_graph`: in the normal form, `G (ψ (ball c ρ))` is the graph
  `{y | Q y ∈ ball c.1 ρ ∧ k (Q y) = y}`, the zero set of `y ↦ y - k (Q y)` in `Q⁻¹(ball c.1 ρ)`.

## Proof

`Ψ = (Q ∘ G, S)` has derivative `(Q ∘ L, S)` at `p`, which is injective (a vector killed by both
lies in `K` and is fixed by `S`), hence bijective by rank--nullity, so the inverse function theorem
gives `ψ`.  On `B`, `H = G ∘ ψ` satisfies `Q ∘ dH = fst` (first component of `dΨ`), and
`rank dH = rank dG = r = dim R`; so `Q` is injective on `range dH`, and `dH (0, v) = 0` because
`Q (dH (0, v)) = 0`.  Hence `H` is constant along the convex slices `{w'} × ball`, which is the
normal form with `k w' = H (w', c)`.
-/

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Hironaka.HolomorphicConstantRank

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]


omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- **The image in the normal form** is a graph: if `Q ∘ k = id` on `ball c.1 ρ` and
`G (ψ w) = k w.1` on `ball c ρ`, then `G (ψ (ball c ρ))` is the set of `y` with `Q y ∈ ball c.1 ρ`
and `k (Q y) = y`, i.e. the zero set of `y ↦ y - k (Q y)` in the open set `Q⁻¹(ball c.1 ρ)`. -/
theorem image_eq_graph {R K : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
    [NormedAddCommGroup K] [NormedSpace ℂ K] {G : E → F} {ψ : R × K → E} {k : R → F}
    {Q : F →L[ℂ] R} {c : R × K} {ρ : ℝ} (hk : ∀ w ∈ ball c.1 ρ, Q (k w) = w)
    (hnf : ∀ w ∈ ball c ρ, G (ψ w) = k w.1) :
    G '' (ψ '' ball c ρ) = {y | Q y ∈ ball c.1 ρ ∧ k (Q y) = y} := by
  ext y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw1 : w.1 ∈ ball c.1 ρ := by
      rw [← ball_prod_same] at hw
      exact hw.1
    rw [hnf w hw]
    exact ⟨(hk _ hw1).symm ▸ hw1, by rw [hk _ hw1]⟩
  · rintro ⟨hy, hky⟩
    have hmem : (Q y, c.2) ∈ ball c ρ := by
      rw [← ball_prod_same]
      exact ⟨hy, mem_ball_self (pos_of_mem_ball hy)⟩
    exact ⟨ψ (Q y, c.2), ⟨_, hmem, rfl⟩, by rw [hnf _ hmem, hky]⟩

end Hironaka.HolomorphicConstantRank
end
