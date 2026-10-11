/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualWeierstrassGermQuotient
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

set_option autoImplicit false

/-! # Actual factoriality of finite-dimensional holomorphic-germ rings

Weierstrass preparation and actual quotient primeness, rather than an
assumed factoriality or principal-hypersurface certificate, prove the
factorial induction.  Nearby primitive families remain a separate task.
-/

noncomputable section
open Filter Topology Polynomial
namespace Hironaka.ActualHolomorphicGermFactoriality
open HolGerm OkaGermRelations ActualWeierstrassGermQuotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem map_distinguished {W : (HolGerm E)[X]} (hW : W.Monic)
    (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0) :
    W.map (HolGerm.eval : HolGerm E →+* ℂ) = X ^ W.natDegree := by
  conv_lhs => rw [hW.as_sum]
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, add_eq_left]
  exact Finset.sum_eq_zero fun j hj => by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      hW0 j (Finset.mem_range.mp hj), Polynomial.C_0, zero_mul]

private theorem coprime_X_of_coeff_zero_ne_zero {P : ℂ[X]} (hP : P.coeff 0 ≠ 0) :
    IsCoprime P X := by
  refine ⟨C (P.coeff 0)⁻¹, -C (P.coeff 0)⁻¹ * P.divX, ?_⟩
  calc
    C (P.coeff 0)⁻¹ * P + (-C (P.coeff 0)⁻¹ * P.divX) * X =
        C (P.coeff 0)⁻¹ * C (P.coeff 0) := by
      linear_combination -C (P.coeff 0)⁻¹ * (X_mul_divX_add P)
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hP, C_1]

/-- An actual divisor of a distinguished monic polynomial whose germ is
a unit is itself an actual unit polynomial. -/
theorem isUnit_of_dvd_distinguished_of_isUnit_shiftEval {W P : (HolGerm E)[X]}
    (hW : W.Monic) (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0)
    (hPW : P ∣ W) (hP : IsUnit (shiftEval 0 P)) : IsUnit P := by
  have hl : IsUnit P.leadingCoeff := isUnit_iff_dvd_one.mpr
    (hW ▸ leadingCoeff_dvd_leadingCoeff hPW)
  have hP0 : HolGerm.eval (P.coeff 0) ≠ 0 := by
    simpa only [eval_shiftEval_zero] using (HolGerm.isUnit_iff_eval_ne_zero _).mp hP
  have hd : P.map (HolGerm.eval : HolGerm E →+* ℂ) ∣ X ^ W.natDegree := by
    obtain ⟨Q, hQ⟩ := hPW
    refine ⟨Q.map (HolGerm.eval : HolGerm E →+* ℂ), ?_⟩
    rw [← map_distinguished hW hW0, hQ, Polynomial.map_mul]
  have hpmap : IsUnit (P.map (HolGerm.eval : HolGerm E →+* ℂ)) :=
    (coprime_X_of_coeff_zero_ne_zero (by rwa [coeff_map])).pow_right.isUnit_of_dvd hd
  have hn : P.natDegree = 0 := by
    rw [← natDegree_map_eq_of_isUnit_leadingCoeff (HolGerm.eval : HolGerm E →+* ℂ) hl]
    exact natDegree_eq_zero_of_isUnit hpmap
  rw [eq_C_of_natDegree_eq_zero hn]
  exact ((HolGerm.isUnit_iff_eval_ne_zero _).mpr hP0).map C

/-- Irreducibility of the genuine distinguished germ reflects to its
actual monic polynomial. -/
theorem irreducible_of_irreducible_shiftEval {W : (HolGerm E)[X]}
    (hW : W.Monic) (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0)
    (h : Irreducible (shiftEval 0 W)) : Irreducible W := by
  refine ⟨fun hu => h.not_isUnit (hu.map (shiftEval 0)), ?_⟩
  intro P Q hPQ
  have hi : IsUnit (shiftEval 0 P) ∨ IsUnit (shiftEval 0 Q) :=
    h.isUnit_or_isUnit (by rw [← (shiftEval 0).map_mul, ← hPQ])
  rcases hi with hp | hq
  · exact Or.inl (isUnit_of_dvd_distinguished_of_isUnit_shiftEval hW hW0
      ⟨Q, hPQ⟩ hp)
  · exact Or.inr (isUnit_of_dvd_distinguished_of_isUnit_shiftEval hW hW0
      ⟨P, hPQ.trans (mul_comm _ _)⟩ hq)

private theorem uniqueFactorizationMonoid_prod [IsNoetherianRing (HolGerm E)]
    [UniqueFactorizationMonoid (HolGerm E)] :
    UniqueFactorizationMonoid (HolGerm (E × ℂ)) := by
  let : IsNoetherianRing (HolGerm (E × ℂ)) :=
    isNoetherianRing_prod_of_division (germWeierstrassDivision E)
  refine { irreducible_iff_prime := ?_ }
  intro g
  constructor
  · intro hg
    obtain ⟨L, q, s, A, hq, hA, hfac⟩ :=
      exists_mul_comapEquiv_eq_prodWeierstrassGerm hg.ne_zero
    let W : (HolGerm E)[X] := X ^ s + ∑ j ∈ Finset.range s, C (A j) * X ^ j
    obtain ⟨hW, hd⟩ := AnalyticProjectionWeierstrass.monic_X_pow_add_sum s A
    have hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0 := by
      intro j hj
      rw [hd] at hj
      have hc : W.coeff j = A j := by
        simp [W, coeff_add, coeff_X_pow, Nat.ne_of_lt hj, hj]
      rw [hc]
      exact hA j hj
    have he : shiftEval 0 W = prodWeierstrassGerm s A := by
      simp only [W, shiftEval, map_zero, add_zero, coe_eval₂RingHom,
        eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C,
        prodWeierstrassGerm]
    have hgL : Irreducible (comapEquiv L g) :=
      (MulEquiv.irreducible_iff (f := (comapEquiv L).toMulEquiv)).mpr hg
    have hgq : Irreducible (q * comapEquiv L g) :=
      (associated_unit_mul_left _ _ hq).symm.irreducible hgL
    have hiW : Irreducible (shiftEval 0 W) := by rwa [he, ← hfac]
    have hpW : Prime W := UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_of_irreducible_shiftEval hW hW0 hiW)
    have hp : Prime (q * comapEquiv L g) := by
      rw [hfac, ← he]
      exact (prime_shiftEval_iff hW hW0).mpr hpW
    exact (MulEquiv.prime_iff (e := (comapEquiv L).toMulEquiv)).mp
      ((associated_unit_mul_left _ _ hq).prime hp)
  · exact fun hp => hp.irreducible

/-- The actual finite-dimensional holomorphic-germ ring is factorial,
proved by genuine Weierstrass preparation and quotient primeness. -/
theorem uniqueFactorizationMonoid_holGerm_euclidean (n : ℕ) :
    UniqueFactorizationMonoid (HolGerm (EuclideanSpace ℂ (Fin n))) := by
  induction n with
  | zero =>
      let : IsNoetherianRing (HolGerm (EuclideanSpace ℂ (Fin 0))) :=
        isNoetherianRing_holGerm_euclidean 0
      refine { irreducible_iff_prime := ?_ }
      intro g
      constructor
      · intro hg
        exfalso
        apply hg.not_isUnit
        rw [HolGerm.isUnit_iff_eval_ne_zero]
        intro hev
        apply hg.ne_zero
        obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
        rw [HolGerm.eval_mk] at hev
        rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
        exact Eventually.of_forall fun z => by
          simp [Subsingleton.elim z 0, hev]
      · exact fun hp => hp.irreducible
  | succ n ih =>
      let : UniqueFactorizationMonoid (HolGerm (EuclideanSpace ℂ (Fin n))) := ih
      let : IsNoetherianRing (HolGerm (EuclideanSpace ℂ (Fin n))) :=
        isNoetherianRing_holGerm_euclidean n
      exact (HolGerm.comapEquiv (euclideanSnocCLE n)).toMulEquiv.uniqueFactorizationMonoid
        uniqueFactorizationMonoid_prod

end Hironaka.ActualHolomorphicGermFactoriality
