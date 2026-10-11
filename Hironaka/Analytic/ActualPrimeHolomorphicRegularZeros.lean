/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualPrimeGermGenericAvoidance
import Hironaka.Analytic.ActualWeierstrassGermQuotient
import Mathlib.Algebra.Polynomial.Derivative

import Hironaka.Analytic.GermCoordinateFirstProjection

set_option autoImplicit false

/-!
# Regular zeros internally produced by the original prime function

The complete mathematical statement and ENTIRE proof precede the import
baseline.  Weierstrass preparation, actual polynomial divisibility recovery
and finite avoidance produce the derivative condition from the original germ.
-/

open Hironaka

noncomputable section
open Set Filter Metric Polynomial
open scoped Topology

namespace Hironaka.ActualPrimeHolomorphicRegularZeros

open HolGerm OkaGermRelations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem not_dvd_shiftEval_derivative {W : (HolGerm E)[X]}
    (hW : W.Monic) (hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0)
    (hd : 0 < W.natDegree) :
    ¬shiftEval 0 W ∣ shiftEval 0 W.derivative := by
  intro hdiv
  have hz : W.derivative = 0 := Polynomial.dvd_derivative_iff.mp
    ((ActualWeierstrassGermQuotient.shiftEval_dvd_iff hW hW0 W.derivative).mp hdiv)
  have hc := congrArg (fun P : (HolGerm E)[X] => P.coeff (W.natDegree - 1)) hz
  have hs : W.natDegree - 1 + 1 = W.natDegree := by omega
  rw [coeff_derivative, hs, coeff_natDegree,
    hW, one_mul, ← Nat.cast_add_one, hs, coeff_zero] at hc
  have hcast := congrArg (HolGerm.eval : HolGerm E →+* ℂ) hc
  simp only [map_natCast, map_zero] at hcast
  exact (Nat.ne_of_gt hd) (Nat.cast_eq_zero.mp hcast)

private theorem exists_mk_coeff_sum (s : Finset ℕ) (e : ℕ → ℕ)
    (a : ℕ → E → ℂ) (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    ∃ hP : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ
        (fun x : E × ℂ => ∑ j ∈ s, a j x.1 * x.2 ^ e j) x,
      HolGerm.mk (fun x : E × ℂ => ∑ j ∈ s, a j x.1 * x.2 ^ e j) hP =
        shiftEval (E := E) 0 (∑ j ∈ s, C (HolGerm.mk (a j) (ha j)) * X ^ e j) := by
  have hterm (j : ℕ) : ∀ᶠ x in 𝓝 (0 : E × ℂ),
      DifferentiableAt ℂ (fun x => a j x.1 * x.2 ^ e j) x :=
    eventually_differentiableAt_mul
      (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) (ha j))
      (eventually_differentiableAt_pow (Eventually.of_forall fun _ => differentiableAt_snd) _)
  refine ⟨eventually_differentiableAt_sum s hterm, ?_⟩
  rw [HolGerm.mk_sum s (fun j (x : E × ℂ) => a j x.1 * x.2 ^ e j) hterm, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [HolGerm.mk_mul (fun x : E × ℂ => a j x.1) (fun x : E × ℂ => x.2 ^ e j)
    (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) (ha j))
    (eventually_differentiableAt_pow (Eventually.of_forall fun _ => differentiableAt_snd) _),
    map_mul]
  simp only [shiftEval, coe_eval₂RingHom, eval₂_C, eval₂_X_pow,
    map_zero, add_zero, ofFst_mk, lastCoord_pow_eq_mk]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem coeff_sum_slice_hasDerivAt (s : Finset ℕ) (a : ℕ → E → ℂ)
    (z : E) (t : ℂ) :
    HasDerivAt (fun w => ∑ j ∈ s, a j z * w ^ j)
      (∑ j ∈ s, (a j z * (j : ℂ)) * t ^ (j - 1)) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pow j t).const_mul (a j z)).congr_deriv (by ring)

private def coeffFunction (d : ℕ) (b : ℕ → E → ℂ) (x : E × ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), b j x.1 * x.2 ^ j

private def coeffDerivativeFunction (d : ℕ) (b : ℕ → E → ℂ) (x : E × ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), (b j x.1 * (j : ℂ)) * x.2 ^ (j - 1)

private theorem exists_prepared_pair (q : E × ℂ → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq)) :
    ∃ (L : (E × ℂ) ≃L[ℂ] E × ℂ) (u : E × ℂ → ℂ) (d : ℕ)
      (b : ℕ → E → ℂ)
      (_hu : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ u x)
      (_hb : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (b j) z)
      (hP : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (coeffFunction d b) x)
      (hDP : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (coeffDerivativeFunction d b) x),
      u 0 ≠ 0 ∧ coeffFunction d b =ᶠ[𝓝 0] (fun x => u x * q (L x)) ∧
        Prime (HolGerm.mk (coeffFunction d b) hP) ∧
        ¬HolGerm.mk (coeffFunction d b) hP ∣ HolGerm.mk (coeffDerivativeFunction d b) hDP := by
  classical
  obtain ⟨L, U, d, A, hU, hA0, hfac⟩ :=
    HolGerm.exists_mul_comapEquiv_eq_prodWeierstrassGerm hQ.ne_zero
  let W : (HolGerm E)[X] := X ^ d + ∑ j ∈ Finset.range d, C (A j) * X ^ j
  obtain ⟨hW, hdeg⟩ := AnalyticProjectionWeierstrass.monic_X_pow_add_sum d A
  have hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0 := by
    intro j hj
    rw [hdeg] at hj
    have hc : W.coeff j = A j := by
      simp [W, coeff_add, coeff_X_pow, Nat.ne_of_lt hj, hj]
    rw [hc]
    exact hA0 j hj
  have he : shiftEval 0 W = prodWeierstrassGerm d A := by
    simp only [W, shiftEval, map_zero, add_zero, coe_eval₂RingHom,
      eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C, prodWeierstrassGerm]
  have hQL : Prime (comapEquiv L (HolGerm.mk q hq)) :=
    (MulEquiv.prime_iff (e := (comapEquiv L).toMulEquiv)).mpr hQ
  have hWP : Prime (shiftEval 0 W) := by
    rw [he, ← hfac]
    exact (associated_unit_mul_left _ _ hU).symm.prime hQL
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hW1 : W = 1 := by simp [W, hd0]
    rw [hW1, map_one] at hWP
    exact hWP.not_isUnit isUnit_one
  have hnd := not_dvd_shiftEval_derivative hW hW0 (by rwa [hdeg])
  choose a ha hArep using fun j => HolGerm.exists_eq_mk (A j)
  let b : ℕ → E → ℂ := fun j => if j = d then fun _ => 1 else a j
  have hb (j : ℕ) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (b j) z := by
    by_cases hj : j = d
    · simp only [b, if_pos hj]
      exact Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ)
    · simpa only [b, if_neg hj] using ha j
  have hbmk (j : ℕ) : HolGerm.mk (b j) (hb j) = if j = d then 1 else A j := by
    by_cases hj : j = d
    · simp only [b, if_pos hj]
      rw [HolGerm.mk_const, map_one]
    · simpa only [b, if_neg hj] using (hArep j).symm
  have hpoly : (∑ j ∈ Finset.range (d + 1), C (HolGerm.mk (b j) (hb j)) * X ^ j) = W := by
    rw [Finset.sum_range_succ, hbmk d, if_pos rfl, C_1, one_mul, add_comm]
    apply congrArg (fun P : (HolGerm E)[X] => X ^ d + P)
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbmk j, if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
  obtain ⟨hP, hPgerm⟩ := exists_mk_coeff_sum (Finset.range (d + 1)) id b hb
  simp only [id_eq] at hPgerm
  rw [hpoly] at hPgerm
  change HolGerm.mk (coeffFunction d b) hP = shiftEval 0 W at hPgerm
  let bD : ℕ → E → ℂ := fun j z => b j z * (j : ℂ)
  have hbD (j : ℕ) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (bD j) z :=
    (hb j).mono fun _ hx => hx.mul_const _
  have hbDmk (j : ℕ) : HolGerm.mk (bD j) (hbD j) = HolGerm.mk (b j) (hb j) * (j : HolGerm E) := by
    rw [HolGerm.mk_mul (b j) (fun _ => (j : ℂ)) (hb j)
      (eventually_differentiableAt_const (j : ℂ)), HolGerm.mk_const]
    congr 1
  obtain ⟨hDP, hDPgerm⟩ := exists_mk_coeff_sum (Finset.range (d + 1)) (fun j => j - 1) bD hbD
  have hDpoly : (∑ j ∈ Finset.range (d + 1), C (HolGerm.mk (bD j) (hbD j)) * X ^ (j - 1)) = W.derivative := by
    rw [← hpoly, derivative_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hbDmk j, derivative_C_mul_X_pow]
  rw [hDpoly] at hDPgerm
  obtain ⟨u, hu, hUrep⟩ := HolGerm.exists_eq_mk U
  have hu0 : u 0 ≠ 0 := by
    have hv := (HolGerm.isUnit_iff_eval_ne_zero _).mp hU
    rwa [hUrep, eval_mk] at hv
  have hqL := eventually_differentiableAt_comp_clm (L : (E × ℂ) →L[ℂ] E × ℂ) hq
  have hpeq : coeffFunction d b =ᶠ[𝓝 0] fun x => u x * q (L x) := by
    apply (HolGerm.mk_eq_mk_iff (f := coeffFunction d b) (g := fun x => u x * q (L x))
      (hf := hP) (hg := eventually_differentiableAt_mul hu hqL)).mp
    rw [hPgerm, he, ← hfac, hUrep, comapEquiv_mk]
    exact (HolGerm.mk_mul u (q ∘ L) hu hqL).symm
  refine ⟨L, u, d, b, hu, hb, hP, hDP, hu0, hpeq, ?_, ?_⟩
  · rwa [hPgerm]
  · change ¬HolGerm.mk (coeffFunction d b) hP ∣
      HolGerm.mk (fun x : E × ℂ => ∑ j ∈ Finset.range (d + 1), bD j x.1 * x.2 ^ (j - 1)) hDP
    rwa [hPgerm, hDPgerm]

private theorem frequently_image_of_linear_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E ≃L[ℂ] F) {P : F → Prop}
    (h : ∃ᶠ x in 𝓝 (0 : E), P (L x)) : ∃ᶠ y in 𝓝 (0 : F), P y := by
  rw [Filter.frequently_iff] at h ⊢
  intro S hS
  have hL : Tendsto L (𝓝 (0 : E)) (𝓝 (0 : F)) := by
    simpa only [map_zero] using L.continuous.tendsto (0 : E)
  obtain ⟨x, hx, hpx⟩ := h (hL.eventually hS)
  exact ⟨L x, hx, hpx⟩

/-- The original prime function internally produces a fixed nonzero
direction and frequent original zeros with nonzero actual derivative. -/
theorem exists_direction_frequently_regular_zeros {m : ℕ}
    (q : EuclideanSpace ℂ (Fin m) × ℂ → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq)) :
    ∃ v : EuclideanSpace ℂ (Fin m) × ℂ, v ≠ 0 ∧
      ∃ᶠ x in 𝓝 0, q x = 0 ∧ DifferentiableAt ℂ q x ∧ fderiv ℂ q x v ≠ 0 := by
  classical
  obtain ⟨L, u, d, b, hu, _hb, hP, hDP, hu0, hpeq, hPP, hnd⟩ := exists_prepared_pair q hq hQ
  let e := euclideanSnocCLE m
  have hPc := eventually_differentiableAt_comp_clm
    (e : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin m) × ℂ) hP
  have hDPc := eventually_differentiableAt_comp_clm
    (e : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin m) × ℂ) hDP
  have hPPc : Prime (HolGerm.mk (fun x => coeffFunction d b (e x)) hPc) := by
    change Prime (comapEquiv e (HolGerm.mk (coeffFunction d b) hP))
    exact (MulEquiv.prime_iff (e := (comapEquiv e).toMulEquiv)).mpr hPP
  have hnot (i : Fin 1) : ¬HolGerm.mk (fun x => coeffFunction d b (e x)) hPc ∣
      HolGerm.mk (fun x => coeffDerivativeFunction d b (e x)) hDPc := by
    intro hdiv
    change comapEquiv e (HolGerm.mk (coeffFunction d b) hP) ∣
      comapEquiv e (HolGerm.mk (coeffDerivativeFunction d b) hDP) at hdiv
    apply hnd
    simpa using (comapEquiv e).symm.map_dvd hdiv
  have hf := ActualPrimeGermGenericAvoidance.frequently_zero_avoiding_finite_family
    (fun x => coeffFunction d b (e x)) hPc hPPc
    (fun _ : Fin 1 => fun x => coeffDerivativeFunction d b (e x)) (fun _ => hDPc) hnot
  have hF : ∃ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin m) × ℂ),
      coeffFunction d b x = 0 ∧ coeffDerivativeFunction d b x ≠ 0 :=
    frequently_image_of_linear_comp e (hf.mono fun _ hx => ⟨hx.1, hx.2 0⟩)
  have hqL : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin m) × ℂ),
      DifferentiableAt ℂ q (L x) :=
    (HolGerm.tendsto_clm_nhds_zero (L : (EuclideanSpace ℂ (Fin m) × ℂ) →L[ℂ]
      EuclideanSpace ℂ (Fin m) × ℂ)).eventually hq
  have huev := (continuousAt_zero_of_eventually_differentiableAt hu).eventually_ne hu0
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hu.and (hqL.and (huev.and hpeq)))
  let v : EuclideanSpace ℂ (Fin m) × ℂ := L (0, 1)
  have hv : v ≠ 0 := by
    intro hv0
    have heq : L (0, 1) = L (0 : EuclideanSpace ℂ (Fin m) × ℂ) := by
      rw [map_zero]
      exact hv0
    exact one_ne_zero (congrArg Prod.snd (L.injective heq))
  refine ⟨v, hv, frequently_image_of_linear_comp L ?_⟩
  apply (hF.and_eventually (ball_mem_nhds (0 : EuclideanSpace ℂ (Fin m) × ℂ) hR)).mono
  rintro x ⟨⟨hpx, hDPx⟩, hx⟩
  obtain ⟨huAt, hqAt, huNe, hpeqX⟩ := hball x hx
  have hqx : q (L x) = 0 := (mul_eq_zero.mp (hpeqX.symm.trans hpx)).resolve_left huNe
  have hslice : HasDerivAt (fun t : ℂ => (x.1, t)) (0, 1) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  have huSlice : HasDerivAt (fun t : ℂ => u (x.1, t)) (fderiv ℂ u x (0, 1)) x.2 := by
    simpa only [Function.comp_def, Prod.mk.eta] using huAt.hasFDerivAt.comp_hasDerivAt x.2 hslice
  have hqSlice : HasDerivAt (fun t : ℂ => q (L (x.1, t))) (fderiv ℂ q (L x) v) x.2 := by
    have hLslice := (L : (EuclideanSpace ℂ (Fin m) × ℂ) →L[ℂ]
      EuclideanSpace ℂ (Fin m) × ℂ).hasFDerivAt.comp_hasDerivAt x.2 hslice
    exact hqAt.hasFDerivAt.comp_hasDerivAt x.2 hLslice
  have hpeqAt : coeffFunction d b =ᶠ[𝓝 x] (fun y => u y * q (L y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (hball y hy).2.2.2
  have hsliceT : Tendsto (fun t : ℂ => (x.1, t)) (𝓝 x.2) (𝓝 x) := by
    simpa only [Prod.mk.eta] using hslice.continuousAt.tendsto
  have hpeqSlice := hsliceT.eventually hpeqAt
  have hformula := (coeff_sum_slice_hasDerivAt (Finset.range (d + 1)) b x.1 x.2).unique
    ((huSlice.mul hqSlice).congr_of_eventuallyEq hpeqSlice)
  change coeffDerivativeFunction d b x = fderiv ℂ u x (0, 1) * q (L x) +
    u x * fderiv ℂ q (L x) v at hformula
  refine ⟨hqx, hqAt, fun hderiv => hDPx ?_⟩
  simpa only [hqx, hderiv, mul_zero, add_zero] using hformula

end Hironaka.ActualPrimeHolomorphicRegularZeros
