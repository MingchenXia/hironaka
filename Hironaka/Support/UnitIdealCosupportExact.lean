/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.IdealPowers

set_option autoImplicit false

/-!
# The order of an ideal sheaf at a point, relative to a submanifold

Blueprint `hir:order` (`blueprint/src/hironaka.tex`, Hironaka phase H1).  Sources:
Włodarczyk 2005 §2.1 (`ord_x(𝓘) := max{i | 𝓘 ⊂ 𝔪_x^i}`, `supp(X, 𝓘, E, μ) = {x | ord_x 𝓘 ≥ μ}`) and
Bierstone--Milman 2008, Definitions 2.1 (the cosupport `{x ∈ N | ord_x 𝓘 ≥ d}` of a marked ideal
`(M, N, E, 𝓘, d)`, with `ord_x 𝓘` the largest `q` such that `𝓘_x ⊂ 𝔪^q_{N,x}`).

## The ambient encoding

An ideal of `𝒪_N`, for a closed submanifold `N ⊆ M`, is represented by an ideal sheaf `𝔞` of `𝒪_M`
(a `GermIdeal`); only the restrictions `g|_N` of its germs matter.  Since `𝒪_{N,x} = 𝒪_{M,x}/𝓘_{N,x}`
and the maximal ideal of `𝒪_{N,x}` is the image of `𝔪_x = 𝓘_{{x}}`, the germ `g|_N` lies in
`𝔪_{N,x}^q` exactly when `g` agrees on `N`, near `x`, with a germ of `𝔪_x^q`.  That is the definition
of `VanishesToOrderOn` below, and it needs no chart and no submanifold structure on `N`.  For `N = M`
it is Włodarczyk's `ord_x`.

## Main declarations

* `pointIdeal x` -- the maximal ideal sheaf `𝔪_x = 𝓘_{{x}}`;
* `VanishesToOrderOn n N x q g` -- `g|_N ∈ 𝔪_{N,x}^q`; `OrderGE n N 𝔞 x q` -- `ord_x(𝔞|_N) ≥ q`;
* `order n N 𝔞 x : ℕ∞` -- `ord_x(𝔞|_N)`, with `le_order_iff`;
* `cosupport n N 𝔞 d` -- `{x ∈ N | ord_x(𝔞|_N) ≥ d}`;
* the elementary facts: `𝔪^{q+1} ⊆ 𝔪^q` (`idealPow_pointIdeal_succ_le`), monotonicity in `q`,
  order `≥ 0` for holomorphic germs, order `≥ 1` iff vanishing at the point
  (`vanishesToOrderOn_one_iff`), `cosupport_zero`, `cosupport_one`, `cosupport_unitIdeal`,
  multiplicativity `𝔪^p 𝔪^q ⊆ 𝔪^{p+q}` (`VanishesToOrderOn.mul`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`, so that those two statements can
later be proved in place from it.

Sorry-free.  The Taylor characterisation of `𝔪_x^q` by vanishing derivatives (needed for
`supp(𝓘, μ) = V(𝓓^{μ-1} 𝓘)`) is the next H1 item, not done here.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.GermIdealOrder

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### The maximal ideal of a point and its powers -/

variable {N : Set M} {x : M} {g : M → ℂ}

variable {𝔞 : GermIdeal n M}

/-- The unit ideal has empty cosupport for every positive mark. -/
theorem cosupport_unitIdeal {d : ℕ} (hd : 1 ≤ d) : cosupport n N (unitIdeal n M) d = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have h1 := (hx.2 (fun _ => (1 : ℂ)) (holomorphicAt_const 1)).mono hd
  have := (vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const (n := n) (M := M) (x := x) 1)).mp h1
  exact one_ne_zero this

end
end Hironaka.GermIdealOrder
