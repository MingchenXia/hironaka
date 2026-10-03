/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.RegularPatchPullback
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Transporting regular patches DOWN a local biholomorphism

Source: CT22, Lemma 4.3 (the identification "`W̃ ∖ E ≅ W ∖ g(E)` carries the absolutely continuous restricted
mass").

This module is the converse, and it is the direction the mass identity ACROSS the centre consumes: a regular patch
`Q` of `W̃`, read at a parameter `v₀` whose point `z = Q(v₀)` is not exceptional, is pushed to a regular patch `P`
of `W` centred at `g z`, with `g (Q v) = P (v - v₀)` for `v` near `v₀`.

Write `F = φ_{g z} ∘ g ∘ φ_{Q.center}⁻¹` for the chart expression of `g`, read in the
preferred chart at the CENTRE of `Q` (not at `z`) and the preferred chart at `g z`.  Since
`z` is not exceptional, `F` is a local biholomorphism at `u₀ = γ_Q(v₀)`, represented by
`Ψ`.  The flattening of `W` at `g z` is `(Φ_Q ∘ Ψ⁻¹) - (v₀, 0)`, so

* `γ_P(v - v₀) = Ψ(γ_Q v) = F(γ_Q v)`, hence `P(v - v₀) = g (Q v)`;
* by the chain rule the restriction of a smooth form `β` along `γ_P` equals the restriction of `g^*β` along `γ_Q`,
  and likewise for `ddᶜ` of smooth functions composed with `g`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

namespace RegularPatchPushforward

open Hironaka.BlowupSequences Hironaka.ClosedIrreducibleAnalyticSubvariety Hironaka.RegularPatchPullback

noncomputable section

variable {n : ℕ}

/-- The inverse of a local holomorphic equivalence, centred at a point of its target. -/
def symmAt {p q : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p)
    (hq : q ∈ Ψ.target) : LocalHolomorphicEquivAt (n := n) q where
  source := Ψ.target
  target := Ψ.source
  isOpen_source := Ψ.isOpen_target
  isOpen_target := Ψ.isOpen_source
  center_mem_source := hq
  toFun := Ψ.invFun
  invFun := Ψ.toFun
  toFun_holomorphic := Ψ.invFun_holomorphic
  invFun_holomorphic := Ψ.toFun_holomorphic
  mapsTo_toFun := Ψ.mapsTo_invFun
  mapsTo_invFun := Ψ.mapsTo_toFun
  left_inv := Ψ.right_inv
  right_inv := Ψ.left_inv

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

end

end RegularPatchPushforward

end Hironaka
