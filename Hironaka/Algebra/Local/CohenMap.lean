/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CoefficientField
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Hironaka.Algebra.Local.Regular
import Mathlib.Combinatorics.Matroid.Init

/-!
# The map `Φ : K⟦X₁, …, X_d⟧ → R̂` of the Cohen structure theorem: construction

Kollár's identification `Ô_{p,X} ≅ k(p)⟦x₁, …, xₙ⟧` [Kol07, Definition 55]: with local
coordinates `x₁, …, x_d` and a coefficient field `K → R̂`
(`Hironaka/Algebra/Local/CoefficientField.lean`), power series in the `Xᵢ` are evaluated at the
`ι(xᵢ) ∈ 𝔪R̂`.  Mathlib's `MvPowerSeries.aeval` is a topological construction and `AdicCompletion`
carries no adic topology in Mathlib, so `Φ` is assembled from its finite levels: for each `n`, `F ↦
(truncTotal n F)(ι x₁, …, ι x_d)` is a `K`-algebra map
`K⟦X⟧ → R̂/𝔪̂ⁿ` (the variables are nilpotent there, so the truncation is harmless — the two
polynomials `truncTotal n (F G)` and `truncTotal n F · truncTotal n G` agree below degree `n`
and every monomial of degree `≥ n` in the `ι xᵢ` vanishes in `R̂/𝔪̂ⁿ`), the levels are
compatible, and `R̂` is `𝔪̂`-adically complete (`IsAdicComplete.liftAlgHom`).  The resulting
`Φ = cohenMap` satisfies `Φ(C k) = σ(k)`, `Φ(Xᵢ) = ι(xᵢ)` and `Φ(F) ≡ (truncTotal n F)(ι x)
(mod 𝔪̂ⁿ)`; its surjectivity is proved in `Hironaka/Algebra/Local/Cohen.lean` and its injectivity in
`Hironaka/Algebra/Local/CohenIso.lean`.  The construction takes any `K`-algebra structure on `R̂`
(`[Algebra (ResidueField R) R̂]`), the chosen coefficient field being the instance
`coefficientAlgebra` for `ℚ ⊆ R`; the completed chart map
(`Hironaka/Algebra/Local/ChartCompletion.lean`) applies it to the transported coefficient field of
the chart's local ring.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

/-! ### Polynomials whose variables lie in an ideal -/

section Vanishing

variable {σ K B : Type*} [CommRing K] [CommRing B] [Algebra K B]

/-- If the variables lie in `J` and every monomial of `P` has degree `≥ n`, then `P(a) ∈ Jⁿ`. -/
theorem aeval_mem_pow_of_degree_le {J : Ideal B} {a : σ → B} (ha : ∀ i, a i ∈ J) {n : ℕ}
    {P : MvPolynomial σ K} (hP : ∀ α ∈ P.support, n ≤ α.degree) :
    MvPolynomial.aeval a P ∈ J ^ n := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (hP α hα) ?_)
  simp only [Finsupp.prod, Finsupp.degree_apply]
  exact prod_pow_mem_pow_sum _ a α J ha

/-- If the variables lie in `J` with `Jⁿ = 0`, two polynomials that agree below degree `n` have
the same value. -/
theorem aeval_eq_of_coeff_eq {J : Ideal B} {a : σ → B} (ha : ∀ i, a i ∈ J) {n : ℕ}
    (hJ : J ^ n = ⊥) {P Q : MvPolynomial σ K}
    (h : ∀ α : σ →₀ ℕ, α.degree < n → P.coeff α = Q.coeff α) :
    MvPolynomial.aeval a P = MvPolynomial.aeval a Q := by
  rw [← sub_eq_zero, ← map_sub, ← Ideal.mem_bot, ← hJ]
  refine aeval_mem_pow_of_degree_le ha fun α hα => ?_
  by_contra hlt
  push Not at hlt
  exact (MvPolynomial.mem_support_iff.mp hα) (by rw [MvPolynomial.coeff_sub, h α hlt, sub_self])

theorem eq_of_pow_zero {S : Type*} [CommRing S] (I : Ideal S) (a b : S ⧸ I ^ 0) : a = b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine Ideal.Quotient.eq.mpr ?_
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- In an `I`-adically separated ring, elements agreeing modulo every `Iⁿ` are equal. -/
theorem eq_of_forall_mk_pow_eq {S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {a b : S} (h : ∀ n, Ideal.Quotient.mk (I ^ n) a = Ideal.Quotient.mk (I ^ n) b) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := I) (a - b) fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp (h n)

end Vanishing

/-! ### The finite levels and the lift -/

section Cohen

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {d : ℕ} (x : Fin d → R)

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- The class of `ι(xᵢ)` in `R̂/𝔪̂ⁿ`. -/
noncomputable def levelVar (n : ℕ) (i : Fin d) : R̂ ⧸ maximalIdeal R̂ ^ n :=
  Ideal.Quotient.mk _ (algebraMap R R̂ (x i))

theorem levelVar_mem (hx : ∀ i, x i ∈ maximalIdeal R) (n : ℕ) (i : Fin d) :
    levelVar R x n i ∈ (maximalIdeal R̂).map (Ideal.Quotient.mk (maximalIdeal R̂ ^ n)) := by
  refine Ideal.mem_map_of_mem _ ?_
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (hx i)

theorem map_maximalIdeal_pow_eq_bot (n : ℕ) :
    ((maximalIdeal R̂).map (Ideal.Quotient.mk (maximalIdeal R̂ ^ n))) ^ n = ⊥ := by
  rw [← Ideal.map_pow (Ideal.Quotient.mk (maximalIdeal R̂ ^ n)) (maximalIdeal R̂) n,
    Ideal.map_quotient_self]

/-! The coefficient field enters as a `K`-algebra structure on `R̂`, `K = ResidueField R`: any
`[Algebra (ResidueField R) R̂]` serves for the construction of `Φ`; the section property
`IsCoefficientAlgebra R` is needed only from the surjectivity on
(`Hironaka/Algebra/Local/Cohen.lean`). The chosen coefficient field is the instance
`coefficientAlgebra` below. -/

variable [Algebra (ResidueField R) (AdicCompletion (maximalIdeal R) R)]
  (hx : ∀ i, x i ∈ maximalIdeal R)

/-- The level-`n` evaluation `F ↦ (truncTotal n F)(ι x)` in `R̂/𝔪̂ⁿ`. -/
noncomputable def levelEval (n : ℕ) :
    MvPowerSeries (Fin d) (ResidueField R) →ₐ[ResidueField R] R̂ ⧸ maximalIdeal R̂ ^ n where
  toFun F := MvPolynomial.aeval (levelVar R x n) (truncTotal n F)
  map_one' := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact eq_of_pow_zero _ _ _
    · change MvPolynomial.aeval (levelVar R x n) (truncTotal n 1) = 1
      rw [truncTotal_one hn.ne', map_one]
  map_mul' F G := by
    change MvPolynomial.aeval (levelVar R x n) (truncTotal n (F * G)) =
      MvPolynomial.aeval (levelVar R x n) (truncTotal n F) *
        MvPolynomial.aeval (levelVar R x n) (truncTotal n G)
    rw [← map_mul]
    exact aeval_eq_of_coeff_eq (levelVar_mem R x hx n) (map_maximalIdeal_pow_eq_bot R n)
      fun α hα => by rw [coeff_truncTotal _ hα, coeff_truncTotal_mul_truncTotal_eq_coeff_mul F G hα]
  map_zero' := by
    change MvPolynomial.aeval (levelVar R x n) (truncTotal n 0) = 0
    rw [map_zero, map_zero]
  map_add' F G := by
    change MvPolynomial.aeval (levelVar R x n) (truncTotal n (F + G)) =
      MvPolynomial.aeval (levelVar R x n) (truncTotal n F) +
        MvPolynomial.aeval (levelVar R x n) (truncTotal n G)
    rw [map_add, map_add]
  commutes' k := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact eq_of_pow_zero _ _ _
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      change MvPolynomial.aeval (levelVar R x n) (truncTotal n (k • 1)) = k • 1
      rw [map_smul, truncTotal_one hn.ne', map_smul, map_one]

theorem levelEval_apply (n : ℕ) (F : MvPowerSeries (Fin d) (ResidueField R)) :
    levelEval R x hx n F = MvPolynomial.aeval (levelVar R x n) (truncTotal n F) := rfl

theorem factorₐ_comp_levelVar {m n : ℕ} (hle : m ≤ n) :
    (fun i => Ideal.Quotient.factorₐ (ResidueField R) (I := maximalIdeal R̂ ^ n)
      (J := maximalIdeal R̂ ^ m) (Ideal.pow_le_pow_right hle) (levelVar R x n i)) =
      levelVar R x m := by
  funext i
  unfold levelVar
  exact Ideal.Quotient.factor_mk (S := maximalIdeal R̂ ^ n) (T := maximalIdeal R̂ ^ m)
    (Ideal.pow_le_pow_right hle) _

/-- The levels are compatible. -/
theorem levelEval_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ (ResidueField R) (Ideal.pow_le_pow_right hle)).comp
      (levelEval R x hx n) = levelEval R x hx m := by
  ext1 F
  rw [AlgHom.comp_apply, levelEval_apply, levelEval_apply, MvPolynomial.comp_aeval_apply,
    factorₐ_comp_levelVar R x hle]
  exact aeval_eq_of_coeff_eq (levelVar_mem R x hx m) (map_maximalIdeal_pow_eq_bot R m)
    fun α hα => by rw [coeff_truncTotal _ (lt_of_lt_of_le hα hle), coeff_truncTotal _ hα]

/-- The map `Φ : K⟦X₁, …, X_d⟧ → R̂`, `Xᵢ ↦ ι(xᵢ)`, `K` through the coefficient field: the
identification of [Kol07, Definition 55], as a map. -/
noncomputable def cohenMap : MvPowerSeries (Fin d) (ResidueField R) →ₐ[ResidueField R] R̂ :=
  IsAdicComplete.liftAlgHom (maximalIdeal R̂) (levelEval R x hx)
    (fun hle => levelEval_compat R x hx hle)

theorem mk_cohenMap (n : ℕ) (F : MvPowerSeries (Fin d) (ResidueField R)) :
    Ideal.Quotient.mk (maximalIdeal R̂ ^ n) (cohenMap R x hx F) = levelEval R x hx n F :=
  IsAdicComplete.mk_liftAlgHom (maximalIdeal R̂) (levelEval R x hx)
    (fun hle => levelEval_compat R x hx hle) n F

/-- `Φ(C k) = σ(k)` — the constants go to the coefficient field. -/
theorem cohenMap_C (k : ResidueField R) :
    cohenMap R x hx (C k) = algebraMap (ResidueField R) R̂ k := by
  change cohenMap R x hx
    (algebraMap (ResidueField R) (MvPowerSeries (Fin d) (ResidueField R)) k) = _
  rw [AlgHom.commutes]

/-- `Φ(Xᵢ) = ι(xᵢ)`. -/
theorem cohenMap_X (i : Fin d) : cohenMap R x hx (X i) = algebraMap R R̂ (x i) := by
  refine eq_of_forall_mk_pow_eq (maximalIdeal R̂) fun n => ?_
  rw [mk_cohenMap, levelEval_apply]
  change _ = levelVar R x n i
  rw [← MvPolynomial.aeval_X (R := ResidueField R) (levelVar R x n) i]
  exact aeval_eq_of_coeff_eq (levelVar_mem R x hx n) (map_maximalIdeal_pow_eq_bot R n)
    fun α hα => by rw [coeff_truncTotal _ hα, ← MvPolynomial.coe_X, MvPolynomial.coeff_coe]

end Cohen

section CoefficientAlgebra

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra ℚ R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- `R̂` as an algebra over the residue field through the chosen coefficient field (`ℚ ⊆ R`). -/
noncomputable instance coefficientAlgebra : Algebra (ResidueField R) R̂ :=
  (coefficientField R).toAlgebra

theorem algebraMap_residueField_apply (k : ResidueField R) :
    algebraMap (ResidueField R) R̂ k = coefficientField R k := rfl

/-- The chosen coefficient field is a section of the residue map. -/
theorem isCoefficientAlgebra_coefficientAlgebra : IsCoefficientAlgebra R :=
  residue_coefficientField R

/-- `Φ(C k) = σ(k)` for the chosen coefficient field. -/
theorem cohenMap_C_coefficientField {d : ℕ} (x : Fin d → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (k : ResidueField R) : cohenMap R x hx (C k) = coefficientField R k :=
  cohenMap_C R x hx k

end CoefficientAlgebra

end IsLocalRing
