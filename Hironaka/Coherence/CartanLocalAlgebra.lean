/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.CartanGermReduction
import Hironaka.Analytic.GermParametrizationFunctions
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.GermAlgebraicParametrization
import Hironaka.Analytic.GermCoordinateTower
import Hironaka.Analytic.GermMinimalPolynomial
import Hironaka.Analytic.HolomorphicGermRing
import Hironaka.Analytic.HolomorphicZeroSetThin
set_option autoImplicit false

/-!
# Demailly's Lemma 4.18 at an arbitrary point: the algebra

Demailly, *Complex analytic and differential geometry*, proof of II.4.29 (Cartan's theorem),
second inclusion of (4.30): "If we replace `W_u`, `W_k` by `W_{u,x}`, `W_{k,x}` respectively, the
proof of Lemma 4.18 shows that for every `f ∈ 𝒪_{M,x}` there is a polynomial `R` of degree
`< deg W_{u,x}` with `δ^m f = R(z'; u(z''))` modulo `(W_{u,x}, δ z_k - B_k(z'; u))`."

We work with germs at a point `x`, translated to the origin: `𝒪 = HolGerm ℂⁿ`, `𝒪' = HolGerm ℂᵈ`,
the coordinates `z_k = ξ_k + coord_k`, the linear form `u = u₀ + ℓ` with `ℓ = ∑_{k ≥ d} c_k coord_k`.
Given polynomials `W, E_k` (monic) and `B_k` over `𝒪'`, `δ ∈ 𝒪'`, and an ideal `I ⊆ 𝒪`
containing `W(u)`, `δ z_k - B_k(u)` and `E_k(z_k)` (`d ≤ k`), `exists_local_division` produces
the local Weierstrass factor `W'` of `W(u₀ + T)` (`W(u₀ + T) = W' Q'`, `Q'(0, 0) ≠ 0`) such that
for every germ `g` there is `r` with `deg r < deg W'` and `δ^e g ≡ r(ℓ) (mod I)`,
`e = ∑_k deg E_k` (independent of the point).

Steps: (A) Weierstrass preparation of `E_k(ξ_k + T)` at the origin and reduction with degree
bounds (`CartanGermReduction.exists_reduce_degreeLT`); (B) substitution `δ coord_k ≡ B_k(u) - δ ξ_k`
(`GermParametrizationFunctions.sum_prod_subst`); (C) division by the local factor `W'`.

Unlike Demailly we put the `E_k(z_k)` among the generators (they vanish on `A`), so (4.17) is not
needed here.
-/

open Filter Topology Polynomial

namespace Hironaka.CartanLocalAlgebra

open Hironaka Hironaka.RegularLocusDense
open HolGerm GermAlgebraicParametrization GermMinimalPolynomial

variable {n d : ℕ}

theorem projGerm_constHom (z : ℂ) : projGerm n d (constHom z) = constHom z := rfl

/-- Evaluating a shifted polynomial. -/
theorem evalGerm_comp_X_add_C (F : (HolGerm (ComplexModel d))[X]) (a : ℂ)
    (g : HolGerm (ComplexModel n)) :
    evalGerm n (F.comp (X + C (constHom a))) g = evalGerm n F (constHom a + g) := by
  simp only [evalGerm, eval₂_comp, eval₂_add, eval₂_X, eval₂_C, projGerm_constHom, add_comm]

theorem eval_linearFormGerm (c : Fin n → ℂ) : HolGerm.eval (linearFormGerm n d c) = 0 := by
  rw [linearFormGerm, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs
  · rw [map_mul, coord, coordGerm, eval_mk, map_zero, mul_zero]
  · exact map_zero _

theorem eval_coord (k : Fin n) : HolGerm.eval (coord k) = 0 := by
  simp [coord, coordGerm, HolGerm.eval_mk]

/-- A polynomial whose constant coefficient does not vanish at `0`, evaluated at a germ vanishing
at `0`, is a unit. -/
theorem isUnit_evalGerm {Q : (HolGerm (ComplexModel d))[X]} (hQ : HolGerm.eval (Q.coeff 0) ≠ 0)
    {y : HolGerm (ComplexModel n)} (hy : HolGerm.eval y = 0) : IsUnit (evalGerm n Q y) := by
  rw [isUnit_iff_eval_ne_zero, evalGerm, hom_eval₂, hy, eval₂_at_zero, RingHom.comp_apply,
    eval_projGerm]
  exact hQ

/-- Local Weierstrass factor of a shifted monic polynomial: if `E(ξ + coord_k) ∈ I`, the
Weierstrass factor `E'` of `E(ξ + T)` satisfies `E'(coord_k) ∈ I`. -/
theorem exists_isWeierstrass_mem (I : Ideal (HolGerm (ComplexModel n)))
    {E : (HolGerm (ComplexModel d))[X]} (hE : E.Monic) (a : ℂ) {y : HolGerm (ComplexModel n)}
    (hy : HolGerm.eval y = 0) (hEI : evalGerm n E (constHom a + y) ∈ I) :
    ∃ E' Q' : (HolGerm (ComplexModel d))[X], IsWeierstrass E' ∧ E'.natDegree ≤ E.natDegree ∧
      E.comp (X + C (constHom a)) = E' * Q' ∧ HolGerm.eval (Q'.coeff 0) ≠ 0 ∧
      evalGerm n E' y ∈ I := by
  have hPm : (E.comp (X + C (constHom a))).Monic :=
    hE.comp (monic_X_add_C _) (by rw [natDegree_X_add_C]; exact one_ne_zero)
  obtain ⟨E', Q', hE'm, hE'0, hdeg, hfac, hQ'⟩ := exists_eq_isWeierstrass_mul hPm
  refine ⟨E', Q', ⟨hE'm, hE'0⟩, ?_, hfac, hQ', ?_⟩
  · rw [natDegree_comp, natDegree_X_add_C, mul_one] at hdeg
    exact hdeg
  · have h : evalGerm n (E.comp (X + C (constHom a))) y ∈ I := by
      rw [evalGerm_comp_X_add_C]
      exact hEI
    rw [hfac, evalGerm, eval₂_mul] at h
    exact (Ideal.mul_unit_mem_iff_mem I (isUnit_evalGerm hQ' hy)).1 h

/-- **Demailly's Lemma 4.18 at a point (algebra).** -/
theorem exists_local_division (hdn : d ≤ n) (c ξ : Fin n → ℂ) (u₀ : ℂ)
    {W : (HolGerm (ComplexModel d))[X]} (hW : W.Monic) {E : Fin n → (HolGerm (ComplexModel d))[X]}
    (hE : ∀ k : Fin n, d ≤ k.1 → (E k).Monic) (B : Fin n → (HolGerm (ComplexModel d))[X])
    (δ : HolGerm (ComplexModel d)) (I : Ideal (HolGerm (ComplexModel n)))
    (hWI : evalGerm n W (constHom u₀ + linearFormGerm n d c) ∈ I)
    (hBI : ∀ k : Fin n, d ≤ k.1 → projGerm n d δ * (constHom (ξ k) + coord k) -
      evalGerm n (B k) (constHom u₀ + linearFormGerm n d c) ∈ I)
    (hEI : ∀ k : Fin n, d ≤ k.1 → evalGerm n (E k) (constHom (ξ k) + coord k) ∈ I) :
    ∃ W' Q' : (HolGerm (ComplexModel d))[X], IsWeierstrass W' ∧
      W.comp (X + C (constHom u₀)) = W' * Q' ∧ HolGerm.eval (Q'.coeff 0) ≠ 0 ∧
      ∀ g : HolGerm (ComplexModel n), ∃ r : (HolGerm (ComplexModel d))[X], r.degree < W'.degree ∧
        projGerm n d δ ^ (∑ k, (E k).natDegree) * g - evalGerm n r (linearFormGerm n d c) ∈ I := by
  classical
  set ℓ := linearFormGerm n d c with hℓ
  set U := constHom u₀ + ℓ with hU
  -- (C) the local factor of `W` at `u₀`
  obtain ⟨W', Q', hW', -, hWfac, hQ', hW'I⟩ :=
    exists_isWeierstrass_mem I hW u₀ (eval_linearFormGerm c) hWI
  refine ⟨W', Q', hW', hWfac, hQ', fun g => ?_⟩
  -- (A) local factors of the `E_k` and reduction
  have hEk : ∀ k : Fin n, ∃ p : (HolGerm (ComplexModel d))[X], d ≤ k.1 →
      IsWeierstrass p ∧ p.natDegree ≤ (E k).natDegree ∧ evalGerm n p (coord k) ∈ I := by
    intro k
    by_cases hk : d ≤ k.1
    · obtain ⟨E', -, hE', hdeg, -, -, hE'I⟩ :=
        exists_isWeierstrass_mem I (hE k hk) (ξ k) (eval_coord k) (hEI k hk)
      exact ⟨E', fun _ => ⟨hE', hdeg, hE'I⟩⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose p hp using hEk
  obtain ⟨R, q, hR, hg⟩ := CartanGermReduction.exists_reduce_degreeLT hdn p
    (fun k hk => (hp k hk).1) g
  have hgR : Ideal.Quotient.mk I g =
      Ideal.Quotient.mk I (MvPolynomial.eval₂ (projGerm n d) coord R) := by
    rw [hg, map_add, add_eq_left, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.sum_mem _ fun k _ => by
      split_ifs with hk
      · exact Ideal.mul_mem_left _ _ (hp k hk).2.2
      · exact I.zero_mem
  -- (B) substitution
  set e := ∑ k, (E k).natDegree with he
  set B' : Fin n → (HolGerm (ComplexModel d))[X] := fun k => B k - C (δ * constHom (ξ k))
    with hB'
  set H : (HolGerm (ComplexModel d))[X] := ∑ m ∈ R.support,
    C (R.coeff m * δ ^ (e - ∑ k, m k)) * ∏ k, B' k ^ m k with hH
  have hsub : ∀ k : Fin n, d ≤ k.1 →
      Ideal.Quotient.mk I (evalGerm n (B' k) U) =
        Ideal.Quotient.mk I (projGerm n d δ) * Ideal.Quotient.mk I (coord k) := by
    intro k hk
    have h1 : evalGerm n (B' k) U = evalGerm n (B k) U - projGerm n d δ * constHom (ξ k) := by
      simp only [hB', evalGerm, eval₂_sub, eval₂_mul, eval₂_C, map_mul, projGerm_constHom]
    have h := Ideal.Quotient.eq_zero_iff_mem.2 (hBI k hk)
    rw [h1]
    simp only [map_sub, map_mul, map_add] at h ⊢
    linear_combination -h
  have hdeg : ∀ m ∈ R.support, ∑ k, m k ≤ e := by
    intro m hm
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : d ≤ k.1
    · exact ((hR m hm k).2 hk).le.trans (hp k hk).2.1
    · rw [(hR m hm k).1 (not_le.1 hk)]
      exact Nat.zero_le _
  have hHU : Ideal.Quotient.mk I (evalGerm n H U) =
      Ideal.Quotient.mk I (projGerm n d δ ^ e * g) := by
    rw [map_mul, hgR, MvPolynomial.eval₂_eq']
    simp only [hH, evalGerm, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd, eval₂_pow,
      map_sum, map_mul, map_pow, map_prod]
    rw [GermParametrizationFunctions.sum_prod_subst
      (z := fun k => Ideal.Quotient.mk I (coord k)) _ _ hdeg ?_]
    intro m hm k hk
    have hdk : d ≤ k.1 := not_lt.1 fun h => hk ((hR m hm k).1 h)
    exact hsub k hdk
  -- (C) division by `W'`
  set H' := H.comp (X + C (constHom u₀)) with hH'
  have hH'U : evalGerm n H' ℓ = evalGerm n H U := by
    rw [hH', evalGerm_comp_X_add_C]
  refine ⟨H' %ₘ W', degree_modByMonic_lt _ hW'.1, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hHU, ← hH'U, sub_eq_zero]
  conv_lhs => rw [← modByMonic_add_div H' W']
  rw [evalGerm, eval₂_add, eval₂_mul, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hW'I,
    zero_mul, add_zero]

end Hironaka.CartanLocalAlgebra
