/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.OkaPolynomialRelations
import Hironaka.Analytic.GermMinimalPolynomial
import Hironaka.Analytic.HolomorphicZeroSetThin
import Hironaka.Analytic.GermCoordinateTower
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Analytic.HolomorphicGermRing
set_option autoImplicit false

/-!
# Oka's key lemma for holomorphic germs at an arbitrary point `(z₀, t₀)`

Source: Oka's coherence theorem (Grauert--Remmert, *Coherent analytic sheaves*, Ch. 2 §5;
Demailly, *Complex analytic and differential geometry*, II.3.19--3.20).

Germs at `(z₀, t₀) ∈ E × ℂ` are represented, after translation, by `HolGerm (E × ℂ)` (germs at
`0`), and polynomials in `t` with coefficients holomorphic near `z₀` by `(HolGerm E)[X]`.  The
germ at `(z₀, t₀)` of `(z, t) ↦ P(z)(t)` is then `shiftEval t₀ P`, the evaluation of `P` at the
germ `t₀ + s` of the shifted last coordinate.

* `shiftEval t₀ : (HolGerm E)[X] →+* HolGerm (E × ℂ)`; `shiftEval_eq_comp`:
  `shiftEval t₀ P = shiftEval 0 (P.comp (X + t₀))`.
* `exists_eq_sum_shiftEval_polynomialRelations` — **Oka's key lemma at `(z₀, t₀)`**: if
  `W ∈ (HolGerm E)[X]` is monic and `g_1, …, g_q` have degree `≤ D` with `g_{j₀} = W`, every
  relation `∑ a_j · shiftEval t₀ g_j = 0` among germs at `(z₀, t₀)` is a combination of the germs
  of polynomial relations `∑ P_j g_j = 0` with `deg P_j ≤ 2D`.

## Proof

Shift `t ↦ t + t₀` (`Polynomial.comp (X + C t₀)`, which preserves monicity and degrees).  At
the origin, `W(· + t₀)` splits as `W' W''` with `W'` a Weierstrass polynomial and `W''(0, 0) ≠ 0`
(`GermMinimalPolynomial.exists_eq_isWeierstrass_mul`: preparation at the point, then
polynomial division and uniqueness).  Weierstrass division by `W'` exists
(`HolGerm.exists_eq_mul_prodWeierstrassGerm_add`) and has a unique remainder
(`GermMinimalPolynomial.eq_zero_of_mul_prodWeierstrassGerm_add_eq_zero`).  The algebraic key lemma
`OkaPolynomialRelations.exists_eq_sum_polynomialRelations` gives the polynomial relations in the
shifted variable; shifting them back by `X - C t₀` gives relations among the `g_j`.
-/

open Filter Topology Polynomial

namespace Hironaka.OkaGermRelations

open HolGerm GermMinimalPolynomial OkaPolynomialRelations

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The germ at `(z₀, t₀)` of a polynomial in `t` with coefficients holomorphic near `z₀`,
written at the origin: evaluation at the germ `t₀ + s` of the shifted last coordinate. -/
def shiftEval (t₀ : ℂ) : (HolGerm E)[X] →+* HolGerm (E × ℂ) :=
  eval₂RingHom (ofFst : HolGerm E →+* HolGerm (E × ℂ)) (lastCoord + ofFst (constHom t₀))

/-- The shift `t ↦ t + t₀` as a polynomial. -/
def shiftPoly (t₀ : ℂ) : (HolGerm E)[X] := X + C (constHom t₀)

theorem shiftEval_eq_comp (t₀ : ℂ) (P : (HolGerm E)[X]) :
    shiftEval t₀ P = shiftEval 0 (P.comp (shiftPoly t₀)) := by
  simp only [shiftEval, shiftPoly, coe_eval₂RingHom, eval₂_comp, eval₂_add, eval₂_X, eval₂_C,
    map_zero, add_zero]

theorem comp_shiftPoly_neg (t₀ : ℂ) (P : (HolGerm E)[X]) :
    (P.comp (shiftPoly t₀)).comp (shiftPoly (-t₀)) = P := by
  rw [comp_assoc]
  have : (shiftPoly t₀ : (HolGerm E)[X]).comp (shiftPoly (-t₀)) = X := by
    simp only [shiftPoly, add_comp, X_comp, C_comp, map_neg]
    ring
  rw [this, comp_X]

theorem comp_neg_shiftPoly (t₀ : ℂ) (P : (HolGerm E)[X]) :
    (P.comp (shiftPoly (-t₀))).comp (shiftPoly t₀) = P := by
  simpa only [neg_neg] using comp_shiftPoly_neg (-t₀) P

theorem natDegree_shiftPoly (t₀ : ℂ) : (shiftPoly t₀ : (HolGerm E)[X]).natDegree = 1 :=
  natDegree_X_add_C _

theorem natDegree_comp_shiftPoly (t₀ : ℂ) (P : (HolGerm E)[X]) :
    (P.comp (shiftPoly t₀)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_shiftPoly, mul_one]

theorem monic_comp_shiftPoly {t₀ : ℂ} {P : (HolGerm E)[X]} (hP : P.Monic) :
    (P.comp (shiftPoly t₀)).Monic :=
  hP.comp_X_add_C _

/-- `shiftEval 0 P` is `∑_{j < n} ofFst (P_j) · t^j` for any `n > deg P`. -/
theorem shiftEval_zero_eq_sum {P : (HolGerm E)[X]} {n : ℕ} (hn : P.natDegree < n) :
    shiftEval 0 P = ∑ j ∈ Finset.range n, ofFst (P.coeff j) * lastCoord ^ j := by
  simp only [shiftEval, map_zero, add_zero, coe_eval₂RingHom]
  exact eval₂_eq_sum_range' _ hn _

/-- For a monic `P`, `shiftEval 0 P` is the Weierstrass-type germ with the coefficients of `P`. -/
theorem shiftEval_zero_monic {P : (HolGerm E)[X]} (hP : P.Monic) :
    shiftEval 0 P = prodWeierstrassGerm P.natDegree fun j => P.coeff j := by
  conv_lhs => rw [hP.as_sum]
  simp only [shiftEval, map_zero, add_zero, coe_eval₂RingHom, eval₂_add, eval₂_X_pow,
    eval₂_finsetSum, eval₂_mul, eval₂_C, prodWeierstrassGerm]

/-- Evaluation at the origin of `shiftEval 0 P` is the constant coefficient. -/
theorem eval_shiftEval_zero (P : (HolGerm E)[X]) :
    HolGerm.eval (shiftEval 0 P) = HolGerm.eval (P.coeff 0) := by
  have hlast : HolGerm.eval (lastCoord : HolGerm (E × ℂ)) = 0 := by
    rw [HolGerm.lastCoord, eval_mk]
    rfl
  have hofFst : (HolGerm.eval : HolGerm (E × ℂ) →+* ℂ).comp ofFst = HolGerm.eval := by
    ext g
    simp only [RingHom.comp_apply, HolGerm.ofFst, eval_comap]
  simp only [shiftEval, map_zero, add_zero, coe_eval₂RingHom]
  rw [hom_eval₂, hlast, eval₂_at_zero, hofFst]

/-- **Injectivity of `shiftEval 0`**: a polynomial in `t` with holomorphic coefficients whose
germ vanishes at the origin is zero. -/
theorem shiftEval_zero_injective : Function.Injective (shiftEval (E := E) 0) := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
  have hsum := shiftEval_zero_eq_sum (P := P) (Nat.lt_succ_self P.natDegree)
  have h := eq_zero_of_mul_prodWeierstrassGerm_add_eq_zero (s := P.natDegree + 1)
    (A := fun _ => 0) (fun _ _ => map_zero _) (h := 0) (r := fun j => P.coeff j)
    (by rw [zero_mul, zero_add, ← hsum, hP])
  refine Polynomial.ext fun j => ?_
  rw [coeff_zero]
  by_cases hj : j < P.natDegree + 1
  · exact h j hj
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Weierstrass division by a Weierstrass polynomial `W'`, polynomial form.** -/
theorem exists_eq_mul_shiftEval_add {W' : (HolGerm E)[X]} (hW' : W'.Monic)
    (hW'0 : ∀ j < W'.natDegree, HolGerm.eval (W'.coeff j) = 0) (h : HolGerm (E × ℂ)) :
    ∃ (c : HolGerm (E × ℂ)) (ρ : (HolGerm E)[X]),
      ρ.degree < W'.degree ∧ h = c * shiftEval 0 W' + shiftEval 0 ρ := by
  obtain ⟨c, r, hcr⟩ := exists_eq_mul_prodWeierstrassGerm_add (s := W'.natDegree)
    (A := fun j => W'.coeff j) hW'0 h
  set ρ : (HolGerm E)[X] := ∑ j ∈ Finset.range W'.natDegree, C (r j) * X ^ j with hρ
  have hρdeg : ρ.degree < W'.degree := by
    rw [degree_eq_natDegree hW'.ne_zero]
    refine (degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj => ?_
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)
  refine ⟨c, ρ, hρdeg, ?_⟩
  rw [hcr, shiftEval_zero_monic hW']
  congr 1
  simp only [hρ, shiftEval, map_zero, add_zero, coe_eval₂RingHom, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_X_pow]

/-- **Uniqueness of the remainder** of Weierstrass division by `W'`, polynomial form. -/
theorem eq_zero_of_shiftEval_eq_mul {W' : (HolGerm E)[X]} (hW' : W'.Monic)
    (hW'0 : ∀ j < W'.natDegree, HolGerm.eval (W'.coeff j) = 0) (ρ : (HolGerm E)[X])
    (c : HolGerm (E × ℂ)) (hρ : ρ.degree < W'.degree) (hc : shiftEval 0 ρ = c * shiftEval 0 W') :
    ρ = 0 := by
  by_cases hρ0 : ρ = 0
  · exact hρ0
  have hlt : ρ.natDegree < W'.natDegree := natDegree_lt_natDegree hρ0 hρ
  have h := eq_zero_of_mul_prodWeierstrassGerm_add_eq_zero (s := W'.natDegree)
    (A := fun j => W'.coeff j) hW'0 (h := -c) (r := fun j => ρ.coeff j)
    (by rw [← shiftEval_zero_eq_sum hlt, ← shiftEval_zero_monic hW', hc]; ring)
  refine Polynomial.ext fun j => ?_
  rw [coeff_zero]
  by_cases hj : j < W'.natDegree
  · exact h j hj
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Oka's key lemma at `(z₀, t₀)`.**  If `W ∈ (HolGerm E)[X]` is monic and `g_1, …, g_q` have
degree `≤ D` with `g_{j₀} = W`, every relation `∑ a_j · shiftEval t₀ g_j = 0` among germs at
`(z₀, t₀)` is a combination of the germs of `|ι| + 1` polynomial relations `∑ P_j g_j = 0` with
`deg P_j ≤ 2D`. -/
theorem exists_eq_sum_shiftEval_polynomialRelations (t₀ : ℂ) {W : (HolGerm E)[X]}
    (hW : W.Monic) {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → (HolGerm E)[X]) (j₀ : ι)
    (hg₀ : g j₀ = W) {D : ℕ} (hgD : ∀ j, (g j).natDegree ≤ D) (a : ι → HolGerm (E × ℂ))
    (ha : ∑ j, a j * shiftEval t₀ (g j) = 0) :
    ∃ (c : Option ι → HolGerm (E × ℂ)) (P : Option ι → ι → (HolGerm E)[X]),
      (∀ l j, (P l j).natDegree ≤ 2 * D) ∧ (∀ l, ∑ j, P l j * g j = 0) ∧
        ∀ j, a j = ∑ l, c l * shiftEval t₀ (P l j) := by
  set g' : ι → (HolGerm E)[X] := fun j => (g j).comp (shiftPoly t₀) with hg'
  have hWs : (W.comp (shiftPoly t₀)).Monic := monic_comp_shiftPoly hW
  obtain ⟨W', W'', hW'm, hW'0, -, hfac, hW''⟩ := exists_eq_isWeierstrass_mul hWs
  have hu : IsUnit (shiftEval 0 W'') := by
    rw [isUnit_iff_eval_ne_zero, eval_shiftEval_zero]
    exact hW''
  have ha' : ∑ j, a j * shiftEval 0 (g' j) = 0 := by
    simpa only [hg', ← shiftEval_eq_comp] using ha
  obtain ⟨c, P', hP'deg, hP'rel, hP'eq⟩ := exists_eq_sum_polynomialRelations (shiftEval 0)
    shiftEval_zero_injective hWs hW'm hfac hu (exists_eq_mul_shiftEval_add hW'm hW'0)
    (eq_zero_of_shiftEval_eq_mul hW'm hW'0) g' j₀ (by simp only [hg', hg₀])
    (fun j => by simpa only [hg', natDegree_comp_shiftPoly] using hgD j) a ha'
  refine ⟨c, fun l j => (P' l j).comp (shiftPoly (-t₀)), fun l j => ?_, fun l => ?_,
    fun j => ?_⟩
  · rw [natDegree_comp_shiftPoly]
    exact hP'deg l j
  · have h := congrArg (fun P => P.comp (shiftPoly (-t₀))) (hP'rel l)
    simp only [sum_comp, mul_comp, zero_comp, hg', comp_shiftPoly_neg] at h
    exact h
  · rw [hP'eq j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [shiftEval_eq_comp t₀ ((P' l j).comp _), comp_neg_shiftPoly]

end

end Hironaka.OkaGermRelations
