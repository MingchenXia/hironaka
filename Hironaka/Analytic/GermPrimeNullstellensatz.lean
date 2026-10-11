/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermParametrizationProof
import Hironaka.Analytic.HolomorphicCoefficientPolynomials
import Hironaka.Analytic.HolomorphicZeroSetThin

set_option autoImplicit false

/-!
# Rückert's Nullstellensatz for prime ideals of holomorphic germs

Source: Demailly, *Complex analytic and differential geometry*, II.4.22 (Rückert's
Nullstellensatz), in the prime case, by the local parametrization of II.4.13--4.19.

Let `Q ⊆ 𝒪_n` be a prime ideal of holomorphic germs at `0 ∈ ℂⁿ` and let `f_1, …, f_s` be
functions holomorphic near `0` whose germs lie in `Q`.  Then every germ vanishing on the zero
set `{f_1 = ⋯ = f_s = 0}` near `0` lies in `Q`:

  `vanishingIdeal {z | ∀ j, f_j z = 0} ≤ Q`  (`vanishingIdeal_le_of_isPrime`).

Taking for the `f_j` generators of `Q` this is `𝓘(V(Q)) = Q`.

## Proof

After a linear change of coordinates `Q` is in Noether position over `𝒪_d`
(`exists_isNoetherNormalization`) and carries the algebraic parametrization data
`AlgebraicParametrization Q d` (`GermParametrization.exists_algebraicParametrization`): the
minimal polynomial `W` of a primitive element `u = ∑_{k ≥ d} c_k z_k`, the denominator `δ ≠ 0`
with `δ z_k ≡ B_k(u) mod Q`, the Weierstrass polynomials `Q_k(z', z_k) ∈ Q`, and for `g ∉ Q` a
nonzero `h ∈ 𝒪_d` with `h ∈ (g) + Q`.

* **Graph points lie in the zero set of `Q`** (`eventually_eq_zero_of_mem`,
  `eventually_graphPoint_eq_zero`).  Over a base point `x` with `δ(x) ≠ 0`, every root `t` of
  `W(x, ·)` gives the point `(x, B(x, t)/δ(x))`; every element of `Q` vanishes there.  This is
  the substitution argument of `GermParametrizationFunctions.eventually_complete`, which there
  is stated for the vanishing ideal of a germ; here it is redone for an arbitrary ideal `Q`.
* **The graph points are small** over small `x` (`eventually_norm_graphPoint_lt`): their fibre
  coordinates are roots of the Weierstrass polynomials `Q_k(x, ·)`.
* If `g` vanishes on the zero set but `g ∉ Q`, the `h ∈ (g) + Q` vanishes at all graph points,
  hence `h(x) = 0` wherever `δ(x) ≠ 0` near `0` (a monic `W(x, ·)` of positive degree has a
  root), so `h δ = 0` and `h = 0` in the domain `𝒪_d`: a contradiction.

The generalised substitution lemmas (`eventually_subst`, `eventually_mvSubst`,
`eventually_recover`) are copies of those of `GermParametrizationFunctions` with the vanishing
ideal of a germ replaced by an arbitrary ideal `Q`.
-/

open Set Filter Metric Polynomial
open scoped Topology

namespace Hironaka.GermPrimeNullstellensatz

open RegularLocusDense AnalyticGermDecomposition GermAlgebraicParametrization
  GermParametrizationData
open GermParametrizationFunctions (toGerm toGerm_mk rep mk_rep toGerm_eq_rep
  eventually_differentiableAt_rep rep_zero_eq germ_coe_sum germ_coe_prod germ_coe_add germC
  germC_coe polyGerm polyGerm_C polyGerm_X eventually_dvd coeffFun toGerm_coeff_of_lt
  eventually_differentiableAt_coeffFun coeffFun_zero monicPoly lowPoly eval_monicPoly
  eval_lowPoly polyGerm_monic polyGerm_low exists_polyGerm_eq toGerm_projGerm toGerm_coord
  toGerm_evalGerm toGerm_evalGerm_monic toGerm_evalGerm_low toGerm_linearFormGerm toGerm_mvEval
  pow_add_sum_subst sum_prod_subst mvDeg le_mvDeg)

noncomputable section

/-! ### Substitution, for an arbitrary ideal -/

section Substitution

variable {n d : ℕ} {Q : Ideal (HolGerm (ComplexModel n))} (P : AlgebraicParametrization Q d)

/-- Coefficient functions of `W`. -/
abbrev wF : ℕ → ComplexModel d → ℂ := coeffFun P.minpoly P.minpoly.natDegree

/-- Coefficient functions of `B_k`. -/
abbrev bF (k : Fin n) : ℕ → ComplexModel d → ℂ := coeffFun (P.B k) P.minpoly.natDegree

/-- Coefficient functions of `Q_k`. -/
abbrev eF (k : Fin n) : ℕ → ComplexModel d → ℂ :=
  coeffFun (P.coordPoly k) (P.coordPoly k).natDegree

/-- A representative of `δ`. -/
abbrev dF : ComplexModel d → ℂ := rep P.disc

/-- The function `u = ∑_{k ≥ d} c_k z_k`. -/
abbrev uF : ComplexModel n → ℂ := fibreForm d (fun k _ => P.coef k)

theorem polyGerm_minpoly_eq :
    polyGerm P.minpoly = (monicPoly P.minpoly.natDegree (wF P) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) :=
  polyGerm_monic P.isWeierstrass_minpoly.1

theorem polyGerm_B_eq (k : Fin n) :
    polyGerm (P.B k) = (lowPoly P.minpoly.natDegree (bF P k) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) :=
  polyGerm_low _ (P.natDegree_B_lt k)

theorem eventually_recover :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), ∀ t : ℂ, monicEval P.minpoly.natDegree (wF P) x t = 0 →
      ∑ k : Fin n, (if d ≤ k.1 then P.coef k * lowEval P.minpoly.natDegree (bF P k) x t
        else 0) = dF P x * t := by
  have h := eventually_dvd P.dvd_recover
    (f := fun x => (∑ k : Fin n, if d ≤ k.1 then C (P.coef k) *
      lowPoly P.minpoly.natDegree (bF P k) x else 0) - C (dF P x) * X) ?_
    (polyGerm_minpoly_eq P)
  · refine h.mono fun x hx t ht => ?_
    have h0 := eval_eq_zero_of_dvd_of_eval_eq_zero hx (by rw [eval_monicPoly]; exact ht)
    rw [eval_sub, eval_finsetSum, sub_eq_zero] at h0
    simp only [eval_mul, eval_C, eval_X] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp
    · simp
  · rw [map_sub, map_mul, polyGerm_C, polyGerm_X, toGerm_eq_rep, germC_coe, map_sum]
    show _ = ((fun x => ∑ k : Fin n, if d ≤ k.1 then C (P.coef k) *
      lowPoly P.minpoly.natDegree (bF P k) x else 0 : ComplexModel d → ℂ[X]) :
        Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) -
      ((fun x => C (dF P x) : ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) *
      ((fun _ => X : ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X])
    rw [germ_coe_sum]
    refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun k _ => ?_) rfl
    split_ifs
    · rw [map_mul, polyGerm_C, polyGerm_B_eq]
      rfl
    · rw [map_zero]
      rfl

theorem quotient_mk_evalGerm_B {k : Fin n} (hk : d ≤ k.1) :
    Ideal.Quotient.mk Q (evalGerm n (P.B k) (linearFormGerm n d P.coef)) =
      Ideal.Quotient.mk Q (HolGerm.projGerm n d P.disc) * Ideal.Quotient.mk Q (coord k) := by
  rw [← map_mul, Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
  exact P.disc_mul_sub_mem k hk

/-- The polynomial `E_k(T) = B_k(T)^s + ∑_{i<s} q_i δ^{s-i} B_k(T)^i`, `s = deg Q_k`. -/
def substPoly (k : Fin n) : (HolGerm (ComplexModel d))[X] :=
  P.B k ^ (P.coordPoly k).natDegree + ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
    C ((P.coordPoly k).coeff i * P.disc ^ ((P.coordPoly k).natDegree - i)) * P.B k ^ i

theorem evalGerm_substPoly_mem {k : Fin n} (hk : d ≤ k.1) :
    evalGerm n (substPoly P k) (linearFormGerm n d P.coef) ∈ Q := by
  have hQ := P.coordPoly_mem k hk
  have hQ' : evalGerm n (P.coordPoly k) (coord k) = coord k ^ (P.coordPoly k).natDegree +
      ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
        HolGerm.projGerm n d ((P.coordPoly k).coeff i) * coord k ^ i := by
    conv_lhs => rw [(P.isWeierstrass_coordPoly k hk).1.as_sum]
    simp [evalGerm, eval₂_finsetSum]
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hQ ⊢
  rw [hQ'] at hQ
  simp only [substPoly, evalGerm, eval₂_add, eval₂_pow, eval₂_finsetSum, eval₂_mul, eval₂_C,
    map_add, map_pow, map_sum, map_mul] at hQ ⊢
  rw [pow_add_sum_subst _ _ (quotient_mk_evalGerm_B P hk), hQ, mul_zero]

theorem polyGerm_substPoly {k : Fin n} :
    polyGerm (substPoly P k) = ((fun x => lowPoly P.minpoly.natDegree (bF P k) x ^
      (P.coordPoly k).natDegree + ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
        C (eF P k i x * dF P x ^ ((P.coordPoly k).natDegree - i)) *
          lowPoly P.minpoly.natDegree (bF P k) x ^ i : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) := by
  rw [substPoly, map_add, map_pow, map_sum, polyGerm_B_eq]
  show _ = ((fun x => lowPoly P.minpoly.natDegree (bF P k) x ^
      (P.coordPoly k).natDegree : ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) +
    ((fun x => ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
        C (eF P k i x * dF P x ^ ((P.coordPoly k).natDegree - i)) *
          lowPoly P.minpoly.natDegree (bF P k) x ^ i : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X])
  rw [germ_coe_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i hi => ?_)
  rw [map_mul, map_pow, polyGerm_C, polyGerm_B_eq, map_mul, map_pow,
    toGerm_coeff_of_lt _ (Finset.mem_range.1 hi), toGerm_eq_rep]
  rfl

/-- **The fibre coordinates `B_k(x, t)/δ(x)` over a root `t` of `W(x, ·)` are roots of
`Q_k(x, ·)`.** -/
theorem eventually_subst :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), dF P x ≠ 0 → ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wF P) x t = 0 → ∀ k : Fin n, d ≤ k.1 →
        monicEval (P.coordPoly k).natDegree (eF P k) x
          (lowEval P.minpoly.natDegree (bF P k) x t / dF P x) = 0 := by
  have h : ∀ k : Fin n, ∀ᶠ x in 𝓝 (0 : ComplexModel d), d ≤ k.1 → dF P x ≠ 0 →
      ∀ t : ℂ, monicEval P.minpoly.natDegree (wF P) x t = 0 →
        monicEval (P.coordPoly k).natDegree (eF P k) x
          (lowEval P.minpoly.natDegree (bF P k) x t / dF P x) = 0 := by
    intro k
    by_cases hk : d ≤ k.1
    · refine (eventually_dvd (P.dvd_of_mem _ (evalGerm_substPoly_mem P hk))
        (polyGerm_substPoly P) (polyGerm_minpoly_eq P)).mono fun x hx _ hδ t ht => ?_
      have h0 := eval_eq_zero_of_dvd_of_eval_eq_zero hx (by rw [eval_monicPoly]; exact ht)
      simp only [eval_add, eval_pow, eval_finsetSum, eval_mul, eval_C, eval_lowPoly] at h0
      rw [pow_add_sum_subst _ _ (mul_div_cancel₀ _ hδ).symm] at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδ)
    · exact Eventually.of_forall fun _ h => absurd h hk
  exact (eventually_all.2 h).mono fun x hx hδ t ht k hk => hx k hk hδ t ht

/-- `E_R(T) = ∑_m r_m δ^{e - |m|} ∏_k B_k(T)^{m_k}`, i.e. `δ^e R(z', B(T)/δ)`. -/
def mvSubstPoly (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel d))[X] :=
  ∑ m ∈ R.support, C (R.coeff m * P.disc ^ (mvDeg R - ∑ k, m k)) * ∏ k, P.B k ^ m k

theorem evalGerm_mvSubstPoly_mem (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)))
    (hR : ∀ m ∈ R.support, ∀ i : Fin n, i.1 < d → m i = 0)
    (hmem : MvPolynomial.eval₂ (HolGerm.projGerm n d) coord R ∈ Q) :
    evalGerm n (mvSubstPoly P R) (linearFormGerm n d P.coef) ∈ Q := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem ⊢
  rw [MvPolynomial.eval₂_eq'] at hmem
  simp only [mvSubstPoly, evalGerm, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd,
    eval₂_pow, map_sum, map_mul, map_pow, map_prod] at hmem ⊢
  rw [sum_prod_subst (z := fun k => Ideal.Quotient.mk Q (coord k)) _ _
    (le_mvDeg R) ?_, hmem, mul_zero]
  intro m hm k hk
  exact quotient_mk_evalGerm_B P (not_lt.1 fun h => hk (hR m hm k h))

theorem polyGerm_mvSubstPoly (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    polyGerm (mvSubstPoly P R) = ((fun x => ∑ m ∈ R.support,
      C (rep (R.coeff m) x * dF P x ^ (mvDeg R - ∑ k, m k)) *
        ∏ k, lowPoly P.minpoly.natDegree (bF P k) x ^ m k : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) := by
  rw [mvSubstPoly, map_sum, germ_coe_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_prod, polyGerm_C, map_mul, map_pow, toGerm_eq_rep, toGerm_eq_rep]
  show _ = ((fun x => C (rep (R.coeff m) x * dF P x ^ (mvDeg R - ∑ k, m k)) :
      ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) *
    ((fun x => ∏ k, lowPoly P.minpoly.natDegree (bF P k) x ^ m k : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X])
  rw [germ_coe_prod]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_pow, polyGerm_B_eq]
  rfl

theorem eventually_mvSubst (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)))
    (hR : ∀ m ∈ R.support, ∀ i : Fin n, i.1 < d → m i = 0)
    (hmem : MvPolynomial.eval₂ (HolGerm.projGerm n d) coord R ∈ Q) :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), ∀ t : ℂ, monicEval P.minpoly.natDegree (wF P) x t = 0 →
      ∑ m ∈ R.support, rep (R.coeff m) x * dF P x ^ (mvDeg R - ∑ k, m k) *
        ∏ k, lowEval P.minpoly.natDegree (bF P k) x t ^ m k = 0 := by
  refine (eventually_dvd (P.dvd_of_mem _ (evalGerm_mvSubstPoly_mem P R hR hmem))
    (polyGerm_mvSubstPoly P R) (polyGerm_minpoly_eq P)).mono fun x hx t ht => ?_
  have h0 := eval_eq_zero_of_dvd_of_eval_eq_zero hx (by rw [eval_monicPoly]; exact ht)
  simpa only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_pow, eval_lowPoly] using h0

/-- **Every element of `Q` vanishes at the points described by the parametrization identities**
(`GermParametrizationFunctions.eventually_complete` for an arbitrary ideal): near `0`, at a point
`z` with `δ(z') ≠ 0`, `W(z', u(z)) = 0` and `δ(z') z_k = B_k(z', u(z))` for `k ≥ d`, every
representative of every germ of `Q` vanishes. -/
theorem eventually_eq_zero_of_mem {G : HolGerm (ComplexModel n)} (hG : G ∈ Q)
    {F : ComplexModel n → ℂ} (hF : toGerm G = (F : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), dF P (coordinateProjection n d z) ≠ 0 →
      monicEval P.minpoly.natDegree (wF P) (coordinateProjection n d z) (uF P z) = 0 →
      (∀ k : Fin n, d ≤ k.1 → dF P (coordinateProjection n d z) * z k =
        lowEval P.minpoly.natDegree (bF P k) (coordinateProjection n d z) (uF P z)) →
      F z = 0 := by
  obtain ⟨R, q, hR, hReq⟩ := P.reduce G
  have hRmem : MvPolynomial.eval₂ (HolGerm.projGerm n d) coord R ∈ Q := by
    rw [eq_sub_of_add_eq hReq.symm]
    refine sub_mem hG (Ideal.sum_mem _ fun k _ => ?_)
    split_ifs with hk
    · exact Ideal.mul_mem_left _ _ (P.coordPoly_mem k hk)
    · exact zero_mem _
  have hfun : ∀ᶠ z in 𝓝 (0 : ComplexModel n), F z =
      (∑ m ∈ R.support, rep (R.coeff m) (coordinateProjection n d z) *
        ∏ k, z k ^ m k) +
      ∑ k : Fin n, (if d ≤ k.1 then rep (q k) z * monicEval (P.coordPoly k).natDegree
        (eF P k) (coordinateProjection n d z) (z k) else 0) := by
    refine Germ.coe_eq.1 ?_
    have h := congrArg toGerm hReq
    rw [hF, map_add, toGerm_mvEval, map_sum] at h
    rw [h, germ_coe_add]
    refine congrArg₂ (fun a b : Germ (𝓝 (0 : ComplexModel n)) ℂ => a + b) rfl ?_
    rw [germ_coe_sum (Finset.univ : Finset (Fin n))]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [map_mul, toGerm_eq_rep,
        toGerm_evalGerm_monic (P.isWeierstrass_coordPoly k hk).1 (toGerm_coord k)]
      rfl
    · rw [map_zero]
      rfl
  have hproj := HolGerm.tendsto_clm_nhds_zero (coordinateProjection n d)
  have hmv : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wF P) (coordinateProjection n d z) t = 0 →
      ∑ m ∈ R.support, rep (R.coeff m) (coordinateProjection n d z) *
        dF P (coordinateProjection n d z) ^ (mvDeg R - ∑ k, m k) *
        ∏ k, lowEval P.minpoly.natDegree (bF P k) (coordinateProjection n d z) t ^ m k = 0 :=
    hproj.eventually (eventually_mvSubst P R hR hRmem)
  filter_upwards [hfun, hmv, hproj.eventually (eventually_subst P)] with z hzg hzR hzs hδ hW hB
  have hQk : ∀ k : Fin n, d ≤ k.1 → monicEval (P.coordPoly k).natDegree (eF P k)
      (coordinateProjection n d z) (z k) = 0 := fun k hk => by
    rw [eq_div_of_mul_eq hδ ((mul_comm _ _).trans (hB k hk))]
    exact hzs hδ _ hW k hk
  have hRz : ∑ m ∈ R.support, rep (R.coeff m) (coordinateProjection n d z) *
      ∏ k, z k ^ m k = 0 := by
    have h0 := hzR _ hW
    rw [sum_prod_subst (z := fun k => z k) _ _ (le_mvDeg R) ?_] at h0
    · exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδ)
    · intro m hm k hk
      exact (hB k (not_lt.1 fun h => hk (hR m hm k h))).symm
  rw [hzg, hRz, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hk
  · rw [hQk k hk, mul_zero]
  · rfl

end Substitution

/-! ### Points over the complement of the discriminant -/

section GraphPoints

/-- A monic polynomial of positive degree over `ℂ` has a root. -/
theorem exists_monicEval_eq_zero {E : Type*} {q : ℕ} (hq : 0 < q) (a : ℕ → E → ℂ) (x : E) :
    ∃ t : ℂ, monicEval q a x t = 0 := by
  classical
  set p : ℂ[X] := X ^ q + ∑ j : Fin q, C (a j x) * X ^ (j : ℕ) with hp
  have hmonic : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have heval : monicEval q a x = fun t => p.eval t := by
    funext t
    simp [p, monicEval, Polynomial.eval_finsetSum, Finset.sum_range]
  have hdeg : p.natDegree = q := by
    have := Polynomial.natDegree_add_eq_left_of_degree_lt
      (p := (Polynomial.X : ℂ[X]) ^ q)
      (q := ∑ j : Fin q, Polynomial.C (a j x) * Polynomial.X ^ (j : ℕ))
      (by simpa using Polynomial.degree_sum_fin_lt (fun j : Fin q => a j x))
    simpa [p] using this
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp0, hdeg]
    exact_mod_cast hq.ne')
  exact ⟨t, by rw [heval]; exact ht⟩

variable {n d : ℕ} {Q : Ideal (HolGerm (ComplexModel n))} (P : AlgebraicParametrization Q d)

/-- The point `(x, B(x, t)/δ(x))` over a base point `x` and a root `t` of `W(x, ·)`. -/
def graphPoint (x : ComplexModel d) (t : ℂ) : ComplexModel n :=
  WithLp.toLp 2 fun i =>
    if h : i.1 < d then x ⟨i.1, h⟩ else lowEval P.minpoly.natDegree (bF P i) x t / dF P x

theorem graphPoint_apply (x : ComplexModel d) (t : ℂ) (i : Fin n) :
    graphPoint P x t i =
      if h : i.1 < d then x ⟨i.1, h⟩ else lowEval P.minpoly.natDegree (bF P i) x t / dF P x :=
  rfl

theorem graphPoint_apply_of_le (x : ComplexModel d) (t : ℂ) {k : Fin n} (hk : d ≤ k.1) :
    graphPoint P x t k = lowEval P.minpoly.natDegree (bF P k) x t / dF P x := by
  rw [graphPoint_apply, dif_neg (not_lt.mpr hk)]

theorem coordinateProjection_graphPoint (x : ComplexModel d) (t : ℂ) :
    coordinateProjection n d (graphPoint P x t) = x := by
  ext a
  have ha : a.1 < n := lt_of_lt_of_le a.2 P.le
  simp [coordinateProjection_apply, graphPoint, ha]

/-- At a graph point, the primitive element takes the value `t`. -/
theorem eventually_uF_graphPoint :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), dF P x ≠ 0 → ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wF P) x t = 0 → uF P (graphPoint P x t) = t := by
  filter_upwards [eventually_recover P] with x hrec hδ t ht
  have h := hrec t ht
  simp only [uF, fibreForm]
  calc (∑ k : Fin n, if d ≤ k.1 then P.coef k * graphPoint P x t k else 0)
      = (∑ k : Fin n, if d ≤ k.1 then P.coef k *
          lowEval P.minpoly.natDegree (bF P k) x t else 0) / dF P x := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [graphPoint_apply_of_le P x t hk, mul_div_assoc]
        · rw [zero_div]
    _ = t := by rw [h, mul_div_cancel_left₀ _ hδ]

/-- **The graph points over small base points are small.** -/
theorem eventually_norm_graphPoint_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), dF P x ≠ 0 → ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wF P) x t = 0 → ‖graphPoint P x t‖ < ε := by
  set ε' : ℝ := min (ε / (n + 1)) 1 with hε'def
  have hε' : 0 < ε' := lt_min (by positivity) one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hcoef : ∀ k : Fin n, ∀ᶠ x in 𝓝 (0 : ComplexModel d), d ≤ k.1 →
      ∀ j < (P.coordPoly k).natDegree,
        ‖eF P k j x‖ * (P.coordPoly k).natDegree < ε' ^ (P.coordPoly k).natDegree := by
    intro k
    by_cases hk : d ≤ k.1
    · have hj : ∀ j ∈ Finset.range (P.coordPoly k).natDegree, ∀ᶠ x in 𝓝 (0 : ComplexModel d),
          ‖eF P k j x‖ * (P.coordPoly k).natDegree < ε' ^ (P.coordPoly k).natDegree := by
        intro j _
        have hc : ContinuousAt (eF P k j) 0 :=
          ((eventually_differentiableAt_coeffFun (P.coordPoly k)
            (P.coordPoly k).natDegree).self_of_nhds j).continuousAt
        refine (hc.norm.mul continuousAt_const).eventually_lt continuousAt_const ?_
        have h0 : eF P k j 0 = 0 := coeffFun_zero (P.isWeierstrass_coordPoly k hk).2 j
        show ‖eF P k j 0‖ * _ < _
        rw [h0]
        simp [pow_pos hε']
      filter_upwards [(Finset.eventually_all _).2 hj] with x hx _ j hjs
      exact hx j (Finset.mem_range.2 hjs)
    · exact Eventually.of_forall fun _ h => absurd h hk
  filter_upwards [eventually_all.2 hcoef, eventually_subst P, ball_mem_nhds (0 : ComplexModel d) hε']
    with x hx hsub hxs hδ t ht
  have hxn : ‖x‖ < ε' := by simpa using hxs
  have hcoord : ∀ i : Fin n, ‖graphPoint P x t i‖ < ε' := by
    intro i
    by_cases hi : i.1 < d
    · rw [graphPoint_apply, dif_pos hi]
      exact (PiLp.norm_apply_le x ⟨i.1, hi⟩).trans_lt hxn
    · have hk : d ≤ i.1 := not_lt.mp hi
      rw [graphPoint_apply_of_le P x t hk]
      exact HolomorphicCoefficientPolynomials.norm_lt_of_weierstrass_root hε' hε'1
        (fun j hj => hx i hk j hj) (hsub hδ t ht i hk)
  calc ‖graphPoint P x t‖ ≤ ∑ i, ‖graphPoint P x t i‖ := norm_le_sum_norm _
    _ ≤ ∑ _i : Fin n, ε' := Finset.sum_le_sum fun i _ => (hcoord i).le
    _ = n * ε' := by simp
    _ ≤ n * (ε / (n + 1)) := by gcongr; exact min_le_left _ _
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Every germ of `Q` vanishes at the graph points over small base points.** -/
theorem eventually_graphPoint_eq_zero {G : HolGerm (ComplexModel n)} (hG : G ∈ Q)
    {F : ComplexModel n → ℂ} (hF : toGerm G = (F : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), dF P x ≠ 0 → ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wF P) x t = 0 → F (graphPoint P x t) = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_eq_zero_of_mem P hG hF)
  filter_upwards [eventually_norm_graphPoint_lt P hε, eventually_uF_graphPoint P] with x hsmall hu
    hδ t ht
  have hut := hu hδ t ht
  refine hball _ (mem_ball_zero_iff.2 (hsmall hδ t ht)) ?_ ?_ ?_
  · rw [coordinateProjection_graphPoint]
    exact hδ
  · rw [coordinateProjection_graphPoint, hut]
    exact ht
  · intro k hk
    rw [coordinateProjection_graphPoint, hut, graphPoint_apply_of_le P x t hk,
      mul_div_cancel₀ _ hδ]

end GraphPoints

/-! ### The Nullstellensatz for prime ideals -/

section Nullstellensatz

variable {n : ℕ}

/-- **Rückert's Nullstellensatz in Noether position.**  If `Q` carries algebraic
parametrization data and the germs of `f_1, …, f_s` lie in `Q`, every germ vanishing on
`{f_1 = ⋯ = f_s = 0}` near `0` lies in `Q`. -/
theorem vanishingIdeal_le_of_algebraicParametrization {Q : Ideal (HolGerm (ComplexModel n))}
    {d : ℕ} (P : AlgebraicParametrization Q d) {s : ℕ} (f : Fin s → ComplexModel n → ℂ)
    (hf : ∀ j, ∃ G ∈ Q, toGerm G = (f j : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    vanishingIdeal {z | ∀ j, f j z = 0} ≤ Q := by
  intro φ hφ
  by_contra hφQ
  obtain ⟨g, hg, rfl, hgV⟩ := hφ
  obtain ⟨c, hc0, G, hG⟩ := P.exists_eqn _ hφQ
  have hF : toGerm (HolGerm.projGerm n d c - HolGerm.mk g hg * G) =
      ((fun z => rep c (coordinateProjection n d z) - g z * rep G z : ComplexModel n → ℂ) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
    rw [map_sub, map_mul, toGerm_projGerm, toGerm_eq_rep, toGerm_mk, toGerm_eq_rep]
    rfl
  choose Gf hGf hGfeq using hf
  -- at graph points over small `x` with `δ(x) ≠ 0`: all `f_j`, then `g`, then `c` vanish
  have hbase : ∀ᶠ x in 𝓝 (0 : ComplexModel d), dF P x ≠ 0 → rep c x = 0 := by
    obtain ⟨ε, hε, hgball⟩ := Metric.eventually_nhds_iff_ball.1 hgV
    filter_upwards [eventually_graphPoint_eq_zero P hG hF,
      eventually_all.2 fun j => eventually_graphPoint_eq_zero P (hGf j) (hGfeq j),
      eventually_norm_graphPoint_lt P hε] with x hx hfx hsmall hδ
    obtain ⟨t, ht⟩ := exists_monicEval_eq_zero P.natDegree_minpoly_pos (wF P) x
    have hV : graphPoint P x t ∈ {z | ∀ j, f j z = 0} := fun j => hfx j hδ t ht
    have hg0 : g (graphPoint P x t) = 0 :=
      hgball _ (mem_ball_zero_iff.2 (hsmall hδ t ht)) hV
    have h := hx hδ t ht
    simp only [coordinateProjection_graphPoint, hg0, zero_mul, sub_zero] at h
    exact h
  have hmul : c * P.disc = 0 := by
    rw [← mk_rep c, ← mk_rep P.disc, ← HolGerm.mk_mul, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    filter_upwards [hbase] with x hx
    by_cases hδ : dF P x = 0
    · simp [dF] at hδ
      simp [hδ]
    · simp [hx hδ]
  exact hc0 ((mul_eq_zero.1 hmul).resolve_right P.disc_ne_zero)

/-- **Rückert's Nullstellensatz for prime ideals of `𝒪_n`** (Demailly, CADG II.4.22, prime
case).  If `Q` is prime and the germs of `f_1, …, f_s` lie in `Q`, every germ vanishing on
`{f_1 = ⋯ = f_s = 0}` near `0` lies in `Q`. -/
theorem vanishingIdeal_le_of_isPrime (Q : Ideal (HolGerm (ComplexModel n))) [Q.IsPrime]
    {s : ℕ} (f : Fin s → ComplexModel n → ℂ)
    (hf : ∀ j, ∃ hfj : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f j) z, HolGerm.mk (f j) hfj ∈ Q) :
    vanishingIdeal {z | ∀ j, f j z = 0} ≤ Q := by
  obtain ⟨d, L, hN⟩ := exists_isNoetherNormalization Q
  have : (Q.map (HolGerm.comapEquiv L)).IsPrime := Ideal.map_isPrime_of_equiv _
  obtain ⟨P⟩ := GermParametrization.exists_algebraicParametrization hN
  have h' := vanishingIdeal_le_of_algebraicParametrization P (fun j => f j ∘ L) fun j => by
    obtain ⟨hfj, hmem⟩ := hf j
    refine ⟨HolGerm.comapEquiv L (HolGerm.mk (f j) hfj), Ideal.mem_map_of_equiv _ _ |>.2
      ⟨_, hmem, rfl⟩, ?_⟩
    rw [HolGerm.comapEquiv_mk]
    rfl
  have hset : {z | ∀ j, (f j ∘ L) z = 0} = L ⁻¹' {z | ∀ j, f j z = 0} := rfl
  rw [hset, ← GermParametrization.map_vanishingIdeal_comapEquiv] at h'
  intro φ hφ
  have h1 : HolGerm.comapEquiv L φ ∈ Q.map (HolGerm.comapEquiv L) :=
    h' (Ideal.mem_map_of_mem _ hφ)
  obtain ⟨ψ, hψ, hψeq⟩ := (Ideal.mem_map_of_equiv _ _).1 h1
  rwa [(HolGerm.comapEquiv L).injective hψeq] at hψ

end Nullstellensatz

end

end Hironaka.GermPrimeNullstellensatz
