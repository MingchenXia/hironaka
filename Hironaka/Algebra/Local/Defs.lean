/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# The order of an ideal and regular systems of parameters in a local ring

Two notions read off the maximal ideal `𝔪` of a local ring `R`.

* The **order** of an ideal, `ord I = sup {r : I ≤ 𝔪^r} ∈ ℕ∞`. Kollár defines, for a smooth variety
  `X`, a nonzero ideal sheaf `I` and a point `x` with ideal sheaf `𝔪ₓ`, the order of `I` at `x` as
  `ord_x I := max {r : 𝔪ₓ^r 𝒪_{x,X} ⊇ I 𝒪_{x,X}}`; for a principal ideal `(f)` it is the
  multiplicity of the hypersurface `f = 0` [Kol07, Definition 47]. As a supremum in `ℕ∞` the zero
  ideal has order `⊤` (Kollár assumes `I ≠ 0`; Krull's intersection theorem is what makes the two
  readings agree).
* A **regular system of parameters**: a family `z : Fin n → R` that generates `𝔪` and has as many
  members as the Krull dimension of `R`. In a regular local ring these are the minimal generating
  systems of `𝔪`.
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The order of an ideal** [Kol07, Definition 47]: `ord I = sup {r : I ≤ 𝔪^r} ∈ ℕ∞`.  The
zero ideal has order `⊤`. -/
noncomputable def ord (I : Ideal R) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : I ≤ maximalIdeal R ^ r), (r : ℕ∞)

/-- A family `z : Fin n → R` is a regular system of parameters of the local ring `R`: it
generates the maximal ideal and has as many members as the Krull dimension of `R`. In a
regular local ring these are exactly the minimal generating systems of `𝔪`. -/
def IsRegularSystemOfParameters {n : ℕ} (z : Fin n → R) : Prop :=
  Ideal.span (Set.range z) = maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R

end IsLocalRing
