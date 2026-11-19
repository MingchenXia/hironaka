/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Actual ideal-adic power-series evaluation with original finite-level maps

Closed native proofs adapted from the same-repository Hironaka files
`Algebra/Local/CohenMap.lean`, SHA256 ae10d2f47f731146510593b579c50c1e5e37b4415a924420fab50752980eb484,
and ONLY `Regular.prod_pow_mem_pow_sum` from `Algebra/Local/Regular.lean`,
SHA256 47e99794b456a5dd0b803a658e23c4b209dfaa6d4aeeb027f47a0e30fd170d3f.
The construction is generalized to the SAME arbitrary original complete ideal
and coefficient action. No Hironaka import or coefficient-field existence is used.
-/
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.CohenEvaluation
open MvPowerSeries
set_option maxHeartbeats 200000

private theorem prod_pow_mem_pow_sum {B : Type u} [CommRing B] {ι : Type*}
    (s : Finset ι) (a : ι → B) (k : ι → ℕ) (J : Ideal B) (ha : ∀ i, a i ∈ J) :
    ∏ i ∈ s, a i ^ k i ∈ J ^ (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (ha j) _) ih

section Vanishing
variable {σ : Type*} {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]

/-- The actual total-degree bound places every evaluated monomial in the original ideal power. -/
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

/-- Agreement below the actual nilpotence order gives equality of original evaluations. -/
theorem aeval_eq_of_coeff_eq {J : Ideal B} {a : σ → B} (ha : ∀ i, a i ∈ J) {n : ℕ}
    (hJ : J ^ n = ⊥) {P Q : MvPolynomial σ K}
    (h : ∀ α : σ →₀ ℕ, α.degree < n → P.coeff α = Q.coeff α) :
    MvPolynomial.aeval a P = MvPolynomial.aeval a Q := by
  rw [← sub_eq_zero, ← map_sub, ← Ideal.mem_bot, ← hJ]
  refine aeval_mem_pow_of_degree_le ha fun α hα => ?_
  by_contra hlt
  push Not at hlt
  exact (MvPolynomial.mem_support_iff.mp hα) (by rw [MvPolynomial.coeff_sub, h α hlt, sub_self])

/-- The original zero-order quotient retains its actual zero-ring equality. -/
theorem eq_of_pow_zero (I : Ideal B) (a b : B ⧸ I ^ 0) : a = b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine Ideal.Quotient.eq.mpr ?_
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- Every original ideal-power quotient detects whole equality in the original separated ring. -/
theorem eq_of_forall_mk_pow_eq (I : Ideal B) [IsHausdorff I B]
    {a b : B} (h : ∀ n, Ideal.Quotient.mk (I ^ n) a = Ideal.Quotient.mk (I ^ n) b) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := I) (a - b) fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp (h n)
end Vanishing

section Evaluation
variable {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
  (I : Ideal B) {d : ℕ} (x : Fin d → B)

/-- The literal original variable class in the original quotient ring. -/
def levelVar (n : ℕ) (i : Fin d) : B ⧸ I ^ n := Ideal.Quotient.mk _ (x i)

theorem levelVar_mem (hx : ∀ i, x i ∈ I) (n : ℕ) (i : Fin d) :
    levelVar I x n i ∈ I.map (Ideal.Quotient.mk (I ^ n)) :=
  Ideal.mem_map_of_mem _ (hx i)

theorem map_ideal_pow_eq_bot (n : ℕ) :
    (I.map (Ideal.Quotient.mk (I ^ n))) ^ n = ⊥ := by
  rw [← Ideal.map_pow (Ideal.Quotient.mk (I ^ n)) I n, Ideal.map_quotient_self]

variable (hx : ∀ i, x i ∈ I)

/-- Actual ORIGINAL truncation and variable classes construct the whole finite-level algebra map. -/
def levelEval (n : ℕ) : MvPowerSeries (Fin d) K →ₐ[K] B ⧸ I ^ n where
  toFun F := MvPolynomial.aeval (levelVar I x n) (truncTotal n F)
  map_one' := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact eq_of_pow_zero _ _ _
    · change MvPolynomial.aeval (levelVar I x n) (truncTotal n 1) = 1
      rw [truncTotal_one hn.ne', map_one]
  map_mul' F G := by
    change MvPolynomial.aeval (levelVar I x n) (truncTotal n (F * G)) =
      MvPolynomial.aeval (levelVar I x n) (truncTotal n F) *
        MvPolynomial.aeval (levelVar I x n) (truncTotal n G)
    rw [← map_mul]
    exact aeval_eq_of_coeff_eq (K := K) (a := levelVar I x n)
      (levelVar_mem I x hx n) (map_ideal_pow_eq_bot I n)
      fun α hα => by rw [coeff_truncTotal _ hα, coeff_truncTotal_mul_truncTotal_eq_coeff_mul F G hα]
  map_zero' := by
    change MvPolynomial.aeval (levelVar I x n) (truncTotal n 0) = 0
    rw [map_zero, map_zero]
  map_add' F G := by
    change MvPolynomial.aeval (levelVar I x n) (truncTotal n (F + G)) =
      MvPolynomial.aeval (levelVar I x n) (truncTotal n F) +
        MvPolynomial.aeval (levelVar I x n) (truncTotal n G)
    rw [map_add, map_add]
  commutes' k := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact eq_of_pow_zero _ _ _
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      change MvPolynomial.aeval (levelVar I x n) (truncTotal n (k • 1)) = k • 1
      rw [map_smul, truncTotal_one hn.ne', map_smul, map_one]

theorem levelEval_apply (n : ℕ) (F : MvPowerSeries (Fin d) K) :
    levelEval (K := K) I x hx n F = MvPolynomial.aeval (levelVar I x n) (truncTotal n F) := rfl

theorem factorₐ_comp_levelVar {m n : ℕ} (hle : m ≤ n) :
    (fun i => Ideal.Quotient.factorₐ K (I := I ^ n) (J := I ^ m)
      (Ideal.pow_le_pow_right hle) (levelVar I x n i)) = levelVar I x m := by
  funext i
  unfold levelVar
  exact Ideal.Quotient.factor_mk (S := I ^ n) (T := I ^ m) (Ideal.pow_le_pow_right hle) _

/-- Every ORIGINAL quotient transition commutes with the actual finite-level algebra maps. -/
theorem levelEval_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hle)).comp
      (levelEval (K := K) I x hx n) = levelEval (K := K) I x hx m := by
  ext1 F
  rw [AlgHom.comp_apply, levelEval_apply, levelEval_apply, MvPolynomial.comp_aeval_apply,
    factorₐ_comp_levelVar I x hle]
  exact aeval_eq_of_coeff_eq (K := K) (a := levelVar I x m)
    (levelVar_mem I x hx m) (map_ideal_pow_eq_bot I m)
    fun α hα => by rw [coeff_truncTotal _ (lt_of_lt_of_le hα hle), coeff_truncTotal _ hα]

variable [IsAdicComplete I B]

/-- Actual ORIGINAL adic completeness lifts the explicit compatible quotient maps to the SAME original ring. -/
def cohenMap : MvPowerSeries (Fin d) K →ₐ[K] B :=
  IsAdicComplete.liftAlgHom I (levelEval (K := K) I x hx) (fun hle => levelEval_compat (K := K) I x hx hle)

/-- EVERY original ideal-power quotient retains its exact original truncated evaluation. -/
theorem mkₐ_comp_cohenMap (n : ℕ) :
    (Ideal.Quotient.mkₐ K (I ^ n)).comp (cohenMap (K := K) I x hx) = levelEval (K := K) I x hx n := by
  unfold cohenMap
  exact IsAdicComplete.mkₐ_comp_liftAlgHom I (levelEval (K := K) I x hx)
    (fun hle => levelEval_compat (K := K) I x hx hle) n

/-- EVERY original section value retains its exact original finite-level evaluation. -/
theorem mk_cohenMap (n : ℕ) (F : MvPowerSeries (Fin d) K) :
    Ideal.Quotient.mk (I ^ n) (cohenMap (K := K) I x hx F) = levelEval (K := K) I x hx n F :=
  AlgHom.congr_fun (mkₐ_comp_cohenMap (K := K) I x hx n) F

/-- ORIGINAL constants retain the ENTIRE actual original coefficient action. -/
theorem cohenMap_C (k : K) : cohenMap (K := K) I x hx (C k) = algebraMap K B k := by
  change cohenMap (K := K) I x hx (algebraMap K (MvPowerSeries (Fin d) K) k) = _
  rw [AlgHom.commutes]

/-- EVERY original variable is mapped to the SAME original chosen generator. -/
theorem cohenMap_X (i : Fin d) : cohenMap (K := K) I x hx (MvPowerSeries.X i) = x i := by
  refine eq_of_forall_mk_pow_eq I fun n => ?_
  rw [mk_cohenMap, levelEval_apply]
  change _ = levelVar I x n i
  rw [← MvPolynomial.aeval_X (R := K) (levelVar I x n) i]
  exact aeval_eq_of_coeff_eq (K := K) (a := levelVar I x n)
    (levelVar_mem I x hx n) (map_ideal_pow_eq_bot I n)
    fun α hα => by rw [coeff_truncTotal _ hα, ← MvPolynomial.coe_X, MvPolynomial.coeff_coe]
end Evaluation
end Hironaka.Geometry.ProperSteinProjectiveCech.CohenEvaluation
