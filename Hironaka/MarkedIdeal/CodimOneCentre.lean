/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Blowing up a codimension-one centre inside the support of a marked ideal of maximal order

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.7, Lemma `le:codim1` (Villamayor): "After the blow-up `σ` at
such a component `C ⊆ supp(𝓘, μ)` the induced support `supp(𝓘', μ)` does not intersect the exceptional divisor of
`σ`" -- used in Step 1ba of the algorithm (elimination of the codimension-one components of the support).

Pointwise form: let `C ⊆ cosupp(𝔞, μ)` (`μ ≥ 1`, `𝔞` coherent, orders on the whole manifold) be the centre of the
blowup `π`, of dimension `n - 1` at `x = π z`, and let `ord_x 𝔞 ≤ μ` (`x ∉ cosupp(𝔞, μ + 1)`). Then `z ∉
cosupp(σ^c(𝔞, μ), μ)`. Proof: near `x`, `𝓘_C = (u)` (flattening coordinates, Hadamard); the Hadamard bridge gives `𝔞
⊆ 𝓘_C^μ = (u^μ)`; an element `f = c · u^μ` of `𝔞_x` of order `μ` has `c(x) ≠ 0`; and `u ∘ π = d · h` with `d(z) ≠ 0`
for a local equation `h` of the exceptional divisor (both `u ∘ π` and `h` generate `π^*𝓘_C` at `z`). So `f ∘ π = h^μ
· (c ∘ π) d^μ` and the controlled transform contains the unit `(c ∘ π) d^μ` at `z`.

For a marked ideal of maximal order (`D^μ 𝔞 = 𝒪`) every point has `ord_x 𝔞 ≤ μ`, whence `le:codim1`'s transform half
and its marked-ideal form for the corrected transform.

Not here: the first half of `le:codim1` (the codimension-one components of the support are smooth
and isolated).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOneCentre

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder BlowupFlatCoordinates BlowupControlledTransform BlowupExceptionalDivisor BlowupFunctionTransform BlowupDerivativeIdeal HadamardBridge DerivativeIdeal VanishingIdealCoherent RelativePrincipalizationSpan SimultaneousNormalCrossings MarkedIdeals IdealWeightPowers

noncomputable section

variable {n : ℕ}

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A holomorphic germ vanishing at `x` has order `≥ μ` in its `μ`-th power. -/
theorem vanishesToOrderOn_pow {N : Set X} {x : X} (hxN : x ∈ N) {u : X → ℂ}
    (hu : HolomorphicAt n u x) (hux : u x = 0) :
    ∀ μ : ℕ, VanishesToOrderOn n N x μ (fun y => u y ^ μ)
  | 0 => by simpa using vanishesToOrderOn_zero (N := N) (holomorphicAt_const (1 : ℂ) (x := x))
  | μ + 1 => by
    have h1 : VanishesToOrderOn n N x 1 u := (vanishesToOrderOn_one_iff hxN hu).mpr hux
    simpa [pow_succ] using (vanishesToOrderOn_pow hxN hu hux μ).mul h1

end Local

end

end Hironaka.CodimOneCentre
