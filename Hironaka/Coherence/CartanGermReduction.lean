/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermMinimalPolynomial
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.GermAlgebraicParametrization
import Hironaka.Analytic.GermCoordinateTower
import Hironaka.Analytic.HolomorphicGermRing
set_option autoImplicit false

/-!
# Iterated Weierstrass reduction with degree bounds

Demailly, *Complex analytic and differential geometry*, II.4.14 and the proof of II.4.18.

`GermMinimalPolynomial.exists_reduce` writes every germ `g ∈ 𝒪_n` as
`g = R(z_d, …, z_{n-1}) + ∑_k q_k p_k(z', z_k)` modulo Weierstrass polynomials `p_k ∈ 𝒪_d[T]`.
Lemma 4.18 needs, in addition, the degree bound `deg_{z_k} R < deg p_k` produced by the
successive Weierstrass divisions (it bounds the power of the denominator `δ` needed to substitute
`z_k = B_k(u)/δ`).  `exists_reduce_degreeLT` records it.
-/

open Filter Topology Polynomial

namespace Hironaka.CartanGermReduction

open Hironaka Hironaka.RegularLocusDense
open HolGerm GermAlgebraicParametrization GermMinimalPolynomial

variable {n d : ℕ}

/-- Every monomial of `rename Fin.castSucc R * X (Fin.last n) ^ j` has last exponent `j` and
its other exponents from `R`. -/
theorem mem_support_rename_mul_X_pow {R' : Type*} [CommRing R'] [Nontrivial R']
    (R : MvPolynomial (Fin n) R') (j : ℕ) {m : Fin (n + 1) →₀ ℕ}
    (hm : m ∈ (MvPolynomial.rename Fin.castSucc R * MvPolynomial.X (Fin.last n) ^ j).support) :
    m (Fin.last n) ≤ j ∧ ∀ k : Fin n, ∃ m' ∈ R.support, m k.castSucc ≤ m' k := by
  classical
  have hdeg : ∀ i : Fin (n + 1), m i ≤ MvPolynomial.degreeOf i
      (MvPolynomial.rename Fin.castSucc R * MvPolynomial.X (Fin.last n) ^ j) :=
    fun i => MvPolynomial.monomial_le_degreeOf i hm
  constructor
  · refine (hdeg _).trans ((MvPolynomial.degreeOf_mul_le _ _ _).trans ?_)
    have h1 : MvPolynomial.degreeOf (Fin.last n) (MvPolynomial.rename Fin.castSucc R) = 0 := by
      rw [← Nat.le_zero, MvPolynomial.degreeOf_le_iff]
      intro m' hm'
      rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective n)] at hm'
      obtain ⟨m'', -, rfl⟩ := Finset.mem_image.1 hm'
      rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨k, hk⟩
      exact Fin.castSucc_ne_last k hk
    rw [h1, zero_add]
    exact (MvPolynomial.degreeOf_pow_le _ _ _).trans (by
      rw [MvPolynomial.degreeOf_X]
      simp)
  · intro k
    have hR : R ≠ 0 := by
      rintro rfl
      simp at hm
    have hk := hdeg k.castSucc
    rw [MvPolynomial.degreeOf_mul_X_pow_of_ne _ (Fin.castSucc_ne_last k),
      MvPolynomial.degreeOf_rename_of_injective (Fin.castSucc_injective n),
      MvPolynomial.degreeOf_eq_sup] at hk
    obtain ⟨m', hm', hm'eq⟩ := Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.2 hR) fun m => m k
    exact ⟨m', hm', hk.trans hm'eq.le⟩

/-- **Iterated Weierstrass reduction with degree bounds** (Demailly II.4.14 / 4.18): modulo
Weierstrass polynomials `p_k(z', z_k)`, `d ≤ k < n`, every germ is a polynomial `R` in
`z_d, …, z_{n-1}` over `𝒪_d` with `deg_{z_k} R < deg p_k`. -/
theorem exists_reduce_degreeLT (hdn : d ≤ n) (p : Fin n → (HolGerm (ComplexModel d))[X])
    (hp : ∀ k : Fin n, d ≤ k.1 → IsWeierstrass (p k)) (g : HolGerm (ComplexModel n)) :
    ∃ (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) (q : Fin n → HolGerm (ComplexModel n)),
      (∀ m ∈ R.support, ∀ k : Fin n, (k.1 < d → m k = 0) ∧ (d ≤ k.1 → m k < (p k).natDegree)) ∧
      g = MvPolynomial.eval₂ (projGerm n d) coord R +
        ∑ k : Fin n, if d ≤ k.1 then q k * evalGerm n (p k) (coord k) else 0 := by
  induction n, hdn using Nat.le_induction with
  | base =>
    classical
    refine ⟨MvPolynomial.C g, 0, fun m hm k => ⟨fun _ => ?_, fun hk => absurd k.2 (not_lt.2 hk)⟩,
      ?_⟩
    · rw [MvPolynomial.support_C] at hm
      split_ifs at hm
      · simp at hm
      · rw [Finset.mem_singleton.1 hm]
        rfl
    · rw [MvPolynomial.eval₂_C, projGerm_self, Finset.sum_eq_zero fun k _ => if_neg (not_le.2 k.2),
        add_zero]
  | succ n hdn ih =>
    obtain ⟨hWm, hW0⟩ := hp (Fin.last n) hdn
    obtain ⟨q₀, r, hg⟩ := exists_eq_mul_weierstrassGerm_add (s := (p (Fin.last n)).natDegree)
      (A := fun j => projGerm n d ((p (Fin.last n)).coeff j))
      (fun j hj => by rw [eval_projGerm]; exact hW0 j hj) g
    choose R q hR hq using fun j => ih (fun k => p k.castSucc) (fun k hk => hp k.castSucc hk) (r j)
    refine ⟨∑ j ∈ Finset.range (p (Fin.last n)).natDegree,
        MvPolynomial.rename Fin.castSucc (R j) * MvPolynomial.X (Fin.last n) ^ j,
      Fin.lastCases q₀ fun k => ∑ j ∈ Finset.range (p (Fin.last n)).natDegree,
        projGerm (n + 1) n (q j k) * coord (Fin.last n) ^ j, ?_, ?_⟩
    · intro m hm k
      classical
      obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
      obtain ⟨hlast, hcast⟩ := mem_support_rename_mul_X_pow (R j) j hmj
      induction k using Fin.lastCases with
      | last =>
        refine ⟨fun h => absurd h (by simp; omega), fun _ => ?_⟩
        exact lt_of_le_of_lt hlast (Finset.mem_range.1 hj)
      | cast k =>
        obtain ⟨m', hm', hle⟩ := hcast k
        have := hR j m' hm' k
        simp only [Fin.val_castSucc] at this ⊢
        refine ⟨fun h => Nat.eq_zero_of_le_zero (hle.trans (this.1 h).le), fun h => ?_⟩
        exact lt_of_le_of_lt hle (this.2 h)
    · have hr : ∀ j, projGerm (n + 1) n (r j) =
          MvPolynomial.eval₂ (projGerm (n + 1) d) coord (MvPolynomial.rename Fin.castSucc (R j)) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => d ≤ k.1),
              projGerm (n + 1) n (q j k) * evalGerm (n + 1) (p k.castSucc) (coord k.castSucc) := by
        intro j
        rw [hq j, map_add, projGerm_eval₂_rename hdn, map_sum, Finset.sum_filter]
        refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
        split_ifs
        · rw [map_mul, projGerm_evalGerm hdn, projGerm_coordGerm k.2 n.le_succ]
          rfl
        · exact map_zero _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc,
        if_pos hdn]
      rw [← Finset.sum_filter, evalGerm_coord_last hdn hWm]
      conv_lhs => rw [hg]
      simp only [hr, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      have e : coord (Fin.last n) = coordGerm (n + 1) n n.lt_succ_self := rfl
      rw [e, Finset.sum_comm (s := Finset.range _) (t := Finset.univ.filter _)]
      have hsw : ∀ (x : Fin n) (i : ℕ),
          projGerm (n + 1) n (q i x) * evalGerm (n + 1) (p x.castSucc) (coord x.castSucc) *
            coordGerm (n + 1) n n.lt_succ_self ^ i =
          projGerm (n + 1) n (q i x) * coordGerm (n + 1) n n.lt_succ_self ^ i *
            evalGerm (n + 1) (p x.castSucc) (coord x.castSucc) := fun _ _ => mul_right_comm _ _ _
      simp only [hsw]
      ring

end Hironaka.CartanGermReduction
