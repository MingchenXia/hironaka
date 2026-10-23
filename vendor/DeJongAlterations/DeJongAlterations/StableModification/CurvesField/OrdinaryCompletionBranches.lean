/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Algebra.NodeFieldFormalUVLocal

/-!
# The two branches of the formal node

The formal node `K[[u, v]]/(uv)` (Codex's `FormalUV K`, the completed local ring of an ordinary
double point, `Geometry.IsGeometricOrdinaryDoublePoint`) embeds into the product of the two formal
branches `K[[t]] × K[[t]]`, by restricting a power series to the two coordinate axes
(`u ↦ (t, 0)`, `v ↦ (0, t)`), and its image consists of the pairs with equal constant terms.
This is the case `n = 2` of the description of the completed ordinary `n`-fold point as the ring
of `n`-tuples of power series with equal constant terms in M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification/source/
semi-stable.tex`, App. B, l. 4381–4387).

## Main results

* `axisMap K i`: the restriction `K[[X₀, X₁]] → K[[t]]` to the `i`-th coordinate axis, a
  `K`-algebra map with `coeff n (axisMap K i f) = coeff (single i n) f`.
  `mem_span_X_mul_X_of_axisPair_eq_zero`: a power series vanishing on both axes is divisible by
  `X₀ X₁`.
* `branchMap K : FormalUV K →ₐ[K] K⟦X⟧ × K⟦X⟧` with `branchMap_injective`,
  `constantCoeff_branchMap_fst_eq_snd` (the two constant terms agree) and `exists_branchMap_eq`
  (every pair with equal constant terms is in the image).
* `finrank_quotient_range_branchMap_le_one`: the image of `branchMap` has codimension at most one
  (it is spanned, modulo the image, by `(1, 0)`).
* `not_isDomain_formalUV`: the formal node is not a domain.

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-formal-node-branches`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

open MvPowerSeries
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV

set_option autoImplicit false

universe u

noncomputable section

variable (K : Type u) [Field K]

section Axis

/-- The restriction of a power series in two variables to the `i`-th coordinate axis:
`f ↦ f(t, 0)` for `i = 0` and `f ↦ f(0, t)` for `i = 1`. -/
def axisMap (i : Fin 2) : MvPowerSeries (Fin 2) K →ₐ[K] PowerSeries K where
  toFun f := PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single i n) f
  map_one' := by
    ext n
    simp [MvPowerSeries.coeff_one, PowerSeries.coeff_one, Finsupp.single_eq_zero]
  map_mul' f g := by
    classical
    ext n
    rw [PowerSeries.coeff_mk, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
      PowerSeries.coeff_mul]
    simp
  map_zero' := by
    ext n
    simp
  map_add' f g := by
    ext n
    simp
  commutes' c := by
    ext n
    simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, PowerSeries.coeff_C,
      Finsupp.single_eq_zero]

variable {K}

@[simp]
lemma coeff_axisMap (i : Fin 2) (f : MvPowerSeries (Fin 2) K) (n : ℕ) :
    PowerSeries.coeff n (axisMap K i f) = MvPowerSeries.coeff (Finsupp.single i n) f := by
  change PowerSeries.coeff n (PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single i n) f) = _
  exact PowerSeries.coeff_mk _ _

lemma constantCoeff_axisMap (i : Fin 2) (f : MvPowerSeries (Fin 2) K) :
    PowerSeries.constantCoeff (axisMap K i f) = MvPowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_axisMap, Finsupp.single_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma axisMap_X_self (i : Fin 2) : axisMap K i (X i) = PowerSeries.X := by
  ext n
  rw [coeff_axisMap, MvPowerSeries.coeff_X, PowerSeries.coeff_X]
  by_cases hn : n = 1
  · simp [hn]
  · simp [hn, Finsupp.single_eq_single_iff]

lemma axisMap_X_of_ne {i j : Fin 2} (h : i ≠ j) : axisMap K i (X j) = 0 := by
  ext n
  rw [coeff_axisMap, MvPowerSeries.coeff_X, map_zero]
  simp [Finsupp.single_eq_single_iff, h]

lemma axisMap_X_mul_X (i : Fin 2) : axisMap K i (X 0 * X 1) = 0 := by
  rw [map_mul]
  fin_cases i
  · simp [axisMap_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  · simp [axisMap_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

variable (K) in
/-- The restrictions to both coordinate axes. -/
def axisPair : MvPowerSeries (Fin 2) K →ₐ[K] PowerSeries K × PowerSeries K :=
  (axisMap K 0).prod (axisMap K 1)

@[simp]
lemma axisPair_apply (f : MvPowerSeries (Fin 2) K) :
    axisPair K f = (axisMap K 0 f, axisMap K 1 f) := rfl

/-- An exponent vector in two variables with vanishing second entry lies on the first axis. -/
lemma eq_single_zero_of_apply_one_eq_zero {d : Fin 2 →₀ ℕ} (h : d 1 = 0) :
    d = Finsupp.single 0 (d 0) := by
  ext i
  fin_cases i <;> simp [h]

/-- An exponent vector in two variables with vanishing first entry lies on the second axis. -/
lemma eq_single_one_of_apply_zero_eq_zero {d : Fin 2 →₀ ℕ} (h : d 0 = 0) :
    d = Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp [h]

lemma X_mul_X_eq_monomial :
    (X 0 * X 1 : MvPowerSeries (Fin 2) K) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [X, X, monomial_mul_monomial, mul_one]

/-- **A power series vanishing on both coordinate axes is divisible by `X₀ X₁`.** -/
theorem mem_span_X_mul_X_of_axisPair_eq_zero {f : MvPowerSeries (Fin 2) K}
    (h : axisPair K f = 0) : f ∈ Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin 2) K)} := by
  have h0 : ∀ n, MvPowerSeries.coeff (Finsupp.single 0 n) f = 0 := fun n => by
    have := congrArg (fun w => PowerSeries.coeff n w.1) h
    simpa using this
  have h1 : ∀ n, MvPowerSeries.coeff (Finsupp.single 1 n) f = 0 := fun n => by
    have := congrArg (fun w => PowerSeries.coeff n w.2) h
    simpa using this
  set e : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with he
  let g : MvPowerSeries (Fin 2) K := fun d => MvPowerSeries.coeff (d + e) f
  rw [Ideal.mem_span_singleton']
  refine ⟨g, ?_⟩
  ext d
  rw [mul_comm, X_mul_X_eq_monomial, coeff_monomial_mul]
  split_ifs with hle
  · rw [one_mul]
    change MvPowerSeries.coeff (d - e + e) f = _
    rw [tsub_add_cancel_of_le hle]
  · symm
    have : d 0 = 0 ∨ d 1 = 0 := by
      by_contra hcon
      push Not at hcon
      apply hle
      intro i
      fin_cases i
      · simpa [he] using Nat.one_le_iff_ne_zero.2 hcon.1
      · simpa [he] using Nat.one_le_iff_ne_zero.2 hcon.2
    rcases this with hd | hd
    · rw [eq_single_one_of_apply_zero_eq_zero hd]
      exact h1 _
    · rw [eq_single_zero_of_apply_one_eq_zero hd]
      exact h0 _

end Axis

section Branch

lemma coe_uvPolynomial :
    ((uvPolynomial K : MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) = X 0 * X 1 := by
  simp [uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X]

/-- **The two branches of the formal node**: `K[[u, v]]/(uv) → K[[t]] × K[[t]]`,
`u ↦ (t, 0)`, `v ↦ (0, t)`. -/
def branchMap : FormalUV K →ₐ[K] PowerSeries K × PowerSeries K :=
  Ideal.Quotient.liftₐ _ (axisPair K) fun a ha => by
    rw [coe_uvPolynomial] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, axisPair_apply, axisPair_apply, axisMap_X_mul_X, axisMap_X_mul_X]
    simp

variable {K}

@[simp]
lemma branchMap_mk (f : MvPowerSeries (Fin 2) K) :
    branchMap K (Ideal.Quotient.mk _ f) = axisPair K f := rfl

/-- **The formal node embeds into the product of its two branches.** -/
theorem branchMap_injective : Function.Injective (branchMap K) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [branchMap_mk] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, coe_uvPolynomial]
  exact mem_span_X_mul_X_of_axisPair_eq_zero hy

lemma branchMap_coordinate_zero : branchMap K (coordinate K 0) = (PowerSeries.X, 0) := by
  change branchMap K (Ideal.Quotient.mk _ (X 0)) = _
  rw [branchMap_mk, axisPair_apply, axisMap_X_self, axisMap_X_of_ne (by decide)]

lemma branchMap_coordinate_one : branchMap K (coordinate K 1) = (0, PowerSeries.X) := by
  change branchMap K (Ideal.Quotient.mk _ (X 1)) = _
  rw [branchMap_mk, axisPair_apply, axisMap_X_self, axisMap_X_of_ne (by decide)]

/-- Both branches of an element have the same constant term. -/
theorem constantCoeff_branchMap_fst_eq_snd (y : FormalUV K) :
    PowerSeries.constantCoeff (branchMap K y).1 = PowerSeries.constantCoeff (branchMap K y).2 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [branchMap_mk, axisPair_apply, constantCoeff_axisMap]

/-- **The image of the formal node**: every pair of power series with equal constant terms comes
from the formal node. -/
theorem exists_branchMap_eq (w : PowerSeries K × PowerSeries K)
    (hw : PowerSeries.constantCoeff w.1 = PowerSeries.constantCoeff w.2) :
    ∃ y : FormalUV K, branchMap K y = w := by
  classical
  let F : MvPowerSeries (Fin 2) K := fun d =>
    if d 1 = 0 then PowerSeries.coeff (d 0) w.1
    else if d 0 = 0 then PowerSeries.coeff (d 1) w.2 else 0
  refine ⟨Ideal.Quotient.mk _ F, ?_⟩
  rw [branchMap_mk, axisPair_apply]
  ext n
  · rw [coeff_axisMap]
    change F (Finsupp.single 0 n) = _
    simp [F]
  · rw [coeff_axisMap]
    change F (Finsupp.single 1 n) = _
    by_cases hn : n = 0
    · subst hn
      simp only [F, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply, if_true]
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hw]
    · simp [F, hn]

/-- **The image of the formal node has codimension at most one** in `K[[t]] × K[[t]]`: modulo the
image, everything is a multiple of `(1, 0)`. -/
theorem sub_smul_mem_range_branchMap (w : PowerSeries K × PowerSeries K) :
    w - (PowerSeries.constantCoeff w.1 - PowerSeries.constantCoeff w.2) • (1, 0) ∈
      LinearMap.range (branchMap K).toLinearMap := by
  obtain ⟨y, hy⟩ := exists_branchMap_eq (K := K)
    (w - (PowerSeries.constantCoeff w.1 - PowerSeries.constantCoeff w.2) • (1, 0)) (by
      simp [map_sub, PowerSeries.smul_eq_C_mul])
  exact ⟨y, hy⟩

theorem finrank_quotient_range_branchMap_le_one :
    FiniteDimensional K ((PowerSeries K × PowerSeries K) ⧸
        LinearMap.range (branchMap K).toLinearMap) ∧
      Module.finrank K ((PowerSeries K × PowerSeries K) ⧸
        LinearMap.range (branchMap K).toLinearMap) ≤ 1 := by
  set W := LinearMap.range (branchMap K).toLinearMap
  have hspan : (⊤ : Submodule K ((PowerSeries K × PowerSeries K) ⧸ W)) =
      K ∙ Submodule.Quotient.mk (p := W) ((1 : PowerSeries K), (0 : PowerSeries K)) := by
    refine (Submodule.eq_top_iff'.2 fun q => ?_).symm
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective W q
    rw [Submodule.mem_span_singleton]
    refine ⟨PowerSeries.constantCoeff w.1 - PowerSeries.constantCoeff w.2, ?_⟩
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
    exact sub_smul_mem_range_branchMap w
  have hfd : FiniteDimensional K ((PowerSeries K × PowerSeries K) ⧸ W) := by
    change Module.Finite K _
    rw [Module.finite_def, hspan]
    exact Submodule.fg_span_singleton _
  refine ⟨hfd, ?_⟩
  rw [← finrank_top, hspan]
  refine (finrank_span_le_card _).trans ?_
  simp

/-- The formal node is not a domain (`u · v = 0` with `u, v ≠ 0`). -/
theorem not_isDomain_formalUV : ¬ IsDomain (FormalUV K) := by
  intro h
  have h0 : coordinate K 0 ≠ 0 := fun h0 => by
    have := congrArg (fun y => (branchMap K y).1) h0
    simp [branchMap_coordinate_zero] at this
  have h1 : coordinate K 1 ≠ 0 := fun h1 => by
    have := congrArg (fun y => (branchMap K y).2) h1
    simp [branchMap_coordinate_one] at this
  have hmul : coordinate K 0 * coordinate K 1 = 0 := by
    apply branchMap_injective
    rw [map_mul, branchMap_coordinate_zero, branchMap_coordinate_one, map_zero]
    simp
  exact mul_ne_zero h0 h1 hmul

end Branch

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
