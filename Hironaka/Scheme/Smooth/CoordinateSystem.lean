/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs

/-!
# Coordinate systems as étale maps to affine space: the definitions

Kollár works with "local coordinate systems" `x_1, …, x_n` at a point `p` of a smooth `k`-variety
([Kol07, 95], the proof of Theorem 92), and Włodarczyk makes the notion global on an open `U`:
"étale morphisms `φ_1, φ_2 : U → 𝔸ⁿ` with `φ_1^*(x_i) = u_i`" ([Wlo05, Lemma 2.9.5], step (0) of
the proof). The étale-neighbourhood construction that compares two hypersurfaces of maximal
contact (`Hironaka/Scheme/Smooth/Graph.lean`,
`Hironaka/Resolution/Algebraic/MaximalContact/Theorem92.lean`) needs exactly this reading:

* `EtaleCoordinates f n U`: a **coordinate system** on the affine open `U ⊆ X` over `k`
  (`f : X ⟶ Spec k`) is an `n`-tuple `u = (u_0, …, u_{n-1})` of sections of `𝒪_U` whose
  coordinate morphism `φ_u = toAffineSpace f U u : U ⟶ 𝔸ⁿ_k = Spec k[t_0, …, t_{n-1}]` (the
  morphism with `φ_u^*(t_i) = u_i`, `toAffineSpace_appTop_X`) is étale. The structure
  `EtaleCoordinatesAdapted f n r Z x` is a coordinate system together with a chart around `x` and
  the adaptedness `Z ∩ U = φ_u⁻¹(L)`; here the chart `U` is given and nothing is adapted.
* `ratPoint a`: the `k`-rational point `a = (a_0, …, a_{n-1})` of `𝔸ⁿ_k`, the prime ideal of the
  polynomials vanishing at `a`, the kernel of evaluation `k[t] → k` at `a` (maximal, as the kernel
  of a surjection onto the field `k`); `origin k n` is the point `0`, `t_0 = ⋯ = t_{n-1} = 0`.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A **coordinate system** on the affine open `U`: `n` sections `u_0, …, u_{n-1}` of `𝒪_U` whose
coordinate morphism `φ_u = (u_0, …, u_{n-1}) : U ⟶ 𝔸ⁿ_k` is étale (Kollár's "local coordinate
systems", [Kol07, 95]; Włodarczyk's "étale morphisms `φ : U → 𝔸ⁿ` with `φ^*(x_i) = u_i`" in the
proof of [Wlo05, Lemma 2.9.5]). -/
structure EtaleCoordinates (f : X ⟶ Spec (.of k)) (n : ℕ) (U : X.affineOpens) where
  /-- The coordinate functions `u_0, …, u_{n-1} ∈ Γ(U, 𝒪_U)`. -/
  v : Fin n → Γ(X, U.1)
  /-- The coordinate morphism `φ_u = toAffineSpace f U v : U ⟶ 𝔸ⁿ_k` is étale. -/
  etale : Etale (toAffineSpace f U.1 v)

attribute [instance] EtaleCoordinates.etale

variable (f : X ⟶ Spec (.of k)) {n : ℕ} {U : X.affineOpens}

/-- The coordinate morphism `φ_u : U ⟶ 𝔸ⁿ_k` of a coordinate system `u`. -/
noncomputable abbrev EtaleCoordinates.hom (c : EtaleCoordinates f n U) :
    (U.1 : Scheme.{u}) ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
  toAffineSpace f U.1 c.v

/-- Evaluation at a point of `kⁿ` is onto `k` (constants). -/
theorem surjective_aeval (a : Fin n → k) :
    Function.Surjective (MvPolynomial.aeval (R := k) (S₁ := k) a : MvPolynomial (Fin n) k → k) :=
  fun c => ⟨MvPolynomial.C c, by simp⟩

/-- The **`k`-rational point** `a = (a_0, …, a_{n-1})` of `𝔸ⁿ_k = Spec k[t_0, …, t_{n-1}]` — the
prime (maximal) ideal of the polynomials vanishing at `a`, the kernel of evaluation at `a`. -/
noncomputable def ratPoint (a : Fin n → k) : Spec (.of (MvPolynomial (Fin n) k)) :=
  ⟨RingHom.ker (MvPolynomial.aeval (R := k) (S₁ := k) a),
    (RingHom.ker_isMaximal_of_surjective _ (surjective_aeval a)).isPrime⟩

theorem mem_ratPoint_asIdeal_iff (a : Fin n → k) (p : MvPolynomial (Fin n) k) :
    p ∈ (ratPoint a).asIdeal ↔ MvPolynomial.aeval a p = 0 :=
  RingHom.mem_ker

theorem isMaximal_ratPoint_asIdeal (a : Fin n → k) : (ratPoint a).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (surjective_aeval a)

/-- The **origin** `0 ∈ 𝔸ⁿ_k`, the `k`-point `t_0 = ⋯ = t_{n-1} = 0`. It is the common image of a
point `p` under the coordinate morphisms of two coordinate systems whose members lie in `𝔪_p`
([Kol07, 95]: "Pick local sections `x_1, x_1' ∈ MC(I)`", which lie in `𝔪_p` since the hypersurfaces
of maximal contact pass through `p`). -/
noncomputable abbrev origin (k : Type u) [Field k] (n : ℕ) : Spec (.of (MvPolynomial (Fin n) k)) :=
  ratPoint fun _ : Fin n => (0 : k)

end AlgebraicGeometry
