/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic

set_option autoImplicit false
open Classical
namespace Hironaka.HironakaPDerivStablePolynomialXSaturation
noncomputable section
variable {σ R : Type*} [Field R]

/-- The actual polynomial partial derivative is locally nilpotent on EVERY whole polynomial, with no bound certificate. -/
theorem exists_polynomial_pderiv_pow_zero (i : σ) (P : MvPolynomial σ R) :
    ∃ N : ℕ, ((MvPolynomial.pderiv i).toLinearMap ^ N) P = 0 := by
  let D := (MvPolynomial.pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)).toLinearMap
  have hm : ∀ k : ℕ, ∀ s : σ →₀ ℕ, s i = k → ∀ a : R,
      ∃ N : ℕ, (D ^ N) (MvPolynomial.monomial s a) = 0 := by
    intro k
    induction k with
    | zero =>
      intro s hs a
      refine ⟨1, ?_⟩
      change MvPolynomial.pderiv i (MvPolynomial.monomial s a) = 0
      simp [hs]
    | succ k ih =>
      intro s hs a
      have hk : (s - Finsupp.single i 1 : σ →₀ ℕ) i = k := by simp [hs]
      obtain ⟨N, hN⟩ := ih (s-Finsupp.single i 1) hk (a * (s i : R))
      refine ⟨N+1, ?_⟩
      rw [pow_succ, Module.End.mul_apply]
      change (D ^ N) (MvPolynomial.pderiv i (MvPolynomial.monomial s a)) = 0
      rw [MvPolynomial.pderiv_monomial]
      exact hN
  induction P using MvPolynomial.induction_on' with
  | monomial s a => exact hm (s i) s rfl a
  | add P Q hP hQ =>
    obtain ⟨N, hN⟩ := hP
    obtain ⟨M, hM⟩ := hQ
    refine ⟨N+M, ?_⟩
    rw [map_add]
    have hP' : (D ^ (N+M)) P = 0 := Module.End.pow_map_zero_of_le (by omega) hN
    have hQ' : (D ^ (N+M)) Q = 0 := Module.End.pow_map_zero_of_le (by omega) hM
    rw [hP', hQ', add_zero]

/-- Literal successive pderiv of coordinate multiplication retains the genuine scalar correction. -/
theorem polynomial_pderiv_pow_X_mul (i : σ) (k : ℕ) (P : MvPolynomial σ R) :
    ((MvPolynomial.pderiv i).toLinearMap ^ (k+1)) (MvPolynomial.X i * P) =
      MvPolynomial.X i * ((MvPolynomial.pderiv i).toLinearMap ^ (k+1)) P +
        (k+1 : R) • ((MvPolynomial.pderiv i).toLinearMap ^ k) P := by
  let D := (MvPolynomial.pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)).toLinearMap
  change (D ^ (k+1)) (MvPolynomial.X i * P) =
    MvPolynomial.X i * (D ^ (k+1)) P + (k+1 : R) • (D ^ k) P
  have hpow (m : ℕ) (Q : MvPolynomial σ R) : MvPolynomial.pderiv i ((D ^ m) Q) = (D ^ (m+1)) Q := by
    rw [pow_succ', Module.End.mul_apply]
    rfl
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, Module.End.one_apply]
    change MvPolynomial.pderiv i (MvPolynomial.X i * P) =
      MvPolynomial.X i * MvPolynomial.pderiv i P + (1 : R) • P
    simp [add_comm]
  | succ k ih =>
    have h := congrArg (fun Q => MvPolynomial.pderiv i Q) ih
    simp only [map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
      one_mul, Derivation.map_smul, hpow] at h
    rw [h]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

variable [CharZero R]

/-- An actual pderiv-stable characteristic-zero polynomial ideal is saturated by the SAME coordinate variable. -/
theorem X_mul_mem_iff_of_pderiv_stable (J : Ideal (MvPolynomial σ R)) (i : σ)
    (hD : ∀ P ∈ J, MvPolynomial.pderiv i P ∈ J) (P : MvPolynomial σ R) :
    MvPolynomial.X i * P ∈ J ↔ P ∈ J := by
  refine ⟨?_, J.mul_mem_left _⟩
  intro hXP
  let D := (MvPolynomial.pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)).toLinearMap
  have hiter (k : ℕ) : ∀ Q ∈ J, (D ^ k) Q ∈ J := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro Q hQ
      rw [pow_succ', Module.End.mul_apply]
      exact hD _ (ih Q hQ)
  have hdown (k : ℕ) (hk : (D ^ (k+1)) P ∈ J) : (D ^ k) P ∈ J := by
    have h := hiter (k+1) (MvPolynomial.X i * P) hXP
    rw [polynomial_pderiv_pow_X_mul] at h
    have hmul := J.mul_mem_left (MvPolynomial.X i) hk
    have hc : (k+1 : R) • (D ^ k) P ∈ J := by
      have hsub := J.sub_mem h hmul
      convert hsub using 1
      abel
    have hn : (k+1 : R) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simpa [smul_smul, hn] using (J.restrictScalars R).smul_mem ((k+1 : R)⁻¹) hc
  obtain ⟨N, hN⟩ := exists_polynomial_pderiv_pow_zero i P
  have hbase : (D ^ N) P ∈ J := by rw [hN]; exact J.zero_mem
  have hz : (D ^ 0) P ∈ J := Nat.decreasingInduction
    (motive := fun m _ => (D ^ m) P ∈ J) (fun k _ hk => hdown k hk) hbase (Nat.zero_le N)
  simpa using hz

end
end Hironaka.HironakaPDerivStablePolynomialXSaturation
