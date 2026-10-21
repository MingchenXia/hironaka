/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Rat

/-! Entire polynomial ideals stable under tangent differentiation are genuine
extensions of their contractions to the original normal-coordinate algebra. -/
set_option autoImplicit false

namespace Hironaka.HironakaDifferentialStableCylindricalIdeal

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Differential closure of the entire ideal isolates every actual coefficient. -/
theorem polynomial_C_coeff_mem_of_derivative_stable (J : Ideal R[X])
    (hD : ∀ f ∈ J, derivative f ∈ J) (f : R[X]) (hf : f ∈ J) (m : ℕ) :
    C (f.coeff m) ∈ J := by
  have all : ∀ N : ℕ, ∀ p : R[X], p.natDegree ≤ N → p ∈ J →
      ∀ j : ℕ, C (p.coeff j) ∈ J := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro p hpN hp j
      by_cases hz : p.natDegree = 0
      · by_cases hj : j = 0
        · subst j
          rwa [← Polynomial.eq_C_of_natDegree_eq_zero hz]
        · have hc : p.coeff j = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simpa only [hc, map_zero] using J.zero_mem
      · have hd : p.derivative.natDegree < N :=
          lt_of_lt_of_le (Polynomial.natDegree_derivative_lt hz) hpN
        have positive : ∀ k : ℕ, 0 < k → C (p.coeff k) ∈ J := by
          intro k hk
          obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
          have hm := ih p.derivative.natDegree hd p.derivative le_rfl (hD p hp) a
          rw [Polynomial.coeff_derivative] at hm
          have hn : (a + 1 : ℚ) ≠ 0 := by positivity
          have hinv : algebraMap ℚ R ((a + 1 : ℚ)⁻¹) * (a + 1 : R) = 1 := by
            rw [show (a + 1 : R) = algebraMap ℚ R (a + 1 : ℚ) by simp,
              ← map_mul, inv_mul_cancel₀ hn, map_one]
          have heq : C (algebraMap ℚ R ((a + 1 : ℚ)⁻¹)) *
              C (p.coeff (a + 1) * (a + 1 : R)) = C (p.coeff (a + 1)) := by
            rw [← map_mul]
            congr 1
            calc
              _ = p.coeff (a + 1) *
                  (algebraMap ℚ R ((a + 1 : ℚ)⁻¹) * (a + 1 : R)) := by ring
              _ = _ := by rw [hinv, mul_one]
          simpa only [heq] using
            J.mul_mem_left (C (algebraMap ℚ R ((a + 1 : ℚ)⁻¹))) hm
        have hs : (∑ k ∈ Finset.range p.natDegree,
            C (p.coeff (k + 1)) * X ^ (k + 1)) ∈ J := by
          apply J.sum_mem
          intro k _
          exact J.mul_mem_right _ (positive (k + 1) (by omega))
        have heq : p = (∑ k ∈ Finset.range p.natDegree,
            C (p.coeff (k + 1)) * X ^ (k + 1)) + C (p.coeff 0) := by
          have he := p.as_sum_range_C_mul_X_pow
          rw [Finset.sum_range_succ'] at he
          simpa using he
        by_cases hj : j = 0
        · subst j
          have hsub : p - (∑ k ∈ Finset.range p.natDegree,
              C (p.coeff (k + 1)) * X ^ (k + 1)) = C (p.coeff 0) := by
            exact sub_eq_iff_eq_add.mpr (heq.trans (add_comm _ _))
          simpa only [hsub] using J.sub_mem hp hs
        · exact positive j (Nat.pos_of_ne_zero hj)
  exact all f.natDegree f le_rfl hf m

/-- An entire derivative-stable ideal is extended from its actual coefficients. -/
theorem polynomial_eq_map_C_comap_of_derivative_stable (J : Ideal R[X])
    (hD : ∀ f ∈ J, derivative f ∈ J) :
    J = Ideal.map C (Ideal.comap C J) := by
  apply le_antisymm
  · intro f hf
    rw [f.as_sum_range_C_mul_X_pow]
    apply (Ideal.map C (Ideal.comap C J)).sum_mem
    intro m _
    exact (Ideal.map C (Ideal.comap C J)).mul_mem_right _ (Ideal.mem_map_of_mem C
      (polynomial_C_coeff_mem_of_derivative_stable J hD f hf m))
  · exact Ideal.map_comap_le

private theorem finSuccEquiv_derivative {S : Type*} [CommRing S]
    (n : ℕ) (p : MvPolynomial (Fin (n + 1)) S) :
    derivative (MvPolynomial.finSuccEquiv S n p) =
      MvPolynomial.finSuccEquiv S n (MvPolynomial.pderiv 0 p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MvPolynomial.finSuccEquiv_X_zero, Polynomial.derivative_mul,
        hp, mul_comm]
    · simp [MvPolynomial.finSuccEquiv_X_succ, Polynomial.derivative_mul,
        hp, Fin.succ_ne_zero, mul_comm]

private theorem finSuccEquiv_symm_comp_C {S : Type*} [CommRing S] (n : ℕ) :
    (MvPolynomial.finSuccEquiv S n).symm.toRingHom.comp Polynomial.C =
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom := by
  apply RingHom.ext
  intro p
  apply (MvPolynomial.finSuccEquiv S n).injective
  change MvPolynomial.finSuccEquiv S n
      ((MvPolynomial.finSuccEquiv S n).symm (Polynomial.C p)) =
    MvPolynomial.finSuccEquiv S n (MvPolynomial.rename Fin.succ p)
  rw [AlgEquiv.apply_symm_apply]
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp, MvPolynomial.finSuccEquiv_X_succ]

/-- Closure under every partial derivative extends exactly the actual coefficient ideal. -/
theorem mvPolynomial_eq_map_C_comap_of_pderiv_stable (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) R))
    (hD : ∀ i : Fin n, ∀ f ∈ J, MvPolynomial.pderiv i f ∈ J) :
    J = Ideal.map MvPolynomial.C (Ideal.comap MvPolynomial.C J) := by
  induction n with
  | zero =>
    have hsurj : Function.Surjective (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R) := by
      intro f
      refine ⟨MvPolynomial.isEmptyRingEquiv R (Fin 0) f, ?_⟩
      simpa only [MvPolynomial.isEmptyRingEquiv_symm_apply] using
        (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm_apply_apply f
    exact (Ideal.map_comap_of_surjective MvPolynomial.C hsurj J).symm
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv R n).symm
    let K := Ideal.comap e.toRingHom J
    let r : MvPolynomial (Fin n) R →+* MvPolynomial (Fin (n + 1)) R :=
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom
    let J₁ := Ideal.comap r J
    have hKD : ∀ f ∈ K, derivative f ∈ K := by
      intro f hf
      change e (derivative f) ∈ J
      have heq : e (derivative f) = MvPolynomial.pderiv 0 (e f) := by
        apply (MvPolynomial.finSuccEquiv R n).injective
        simpa only [e, AlgEquiv.apply_symm_apply] using finSuccEquiv_derivative n (e f)
      rw [heq]
      exact hD 0 (e f) hf
    have hK := polynomial_eq_map_C_comap_of_derivative_stable K hKD
    have hJ₁D : ∀ i : Fin n, ∀ f ∈ J₁, MvPolynomial.pderiv i f ∈ J₁ := by
      intro i f hf
      change MvPolynomial.rename Fin.succ (MvPolynomial.pderiv i f) ∈ J
      rw [← MvPolynomial.pderiv_rename (Fin.succ_injective n) i f]
      exact hD i.succ _ hf
    have hJ₁ := ih J₁ hJ₁D
    have hrC : r.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) =
        (MvPolynomial.C : R →+* MvPolynomial (Fin (n + 1)) R) := by
      ext a
      simp [r]
    calc
      J = Ideal.map e.toRingHom K :=
        (Ideal.map_comap_of_surjective e.toRingHom e.surjective J).symm
      _ = Ideal.map r J₁ := by
        rw [hK, Ideal.map_map]
        change Ideal.map (e.toRingHom.comp Polynomial.C)
          (Ideal.comap Polynomial.C (Ideal.comap e.toRingHom J)) = _
        rw [Ideal.comap_comap, finSuccEquiv_symm_comp_C]
      _ = Ideal.map r (Ideal.map MvPolynomial.C (Ideal.comap MvPolynomial.C J₁)) := by
        exact congrArg (Ideal.map r) hJ₁
      _ = Ideal.map MvPolynomial.C (Ideal.comap MvPolynomial.C J) := by
        change Ideal.map r (Ideal.map MvPolynomial.C
          (Ideal.comap MvPolynomial.C (Ideal.comap r J))) = _
        rw [Ideal.map_map, Ideal.comap_comap, hrC]

private theorem sumAlgEquiv_symm_comp_C {S τ : Type*} [CommRing S] (d : ℕ) :
    (MvPolynomial.sumAlgEquiv S (Fin d) τ).symm.toRingHom.comp MvPolynomial.C =
      (MvPolynomial.rename (Sum.inr : τ → Fin d ⊕ τ)).toRingHom := by
  apply RingHom.ext
  intro p
  apply (MvPolynomial.sumAlgEquiv S (Fin d) τ).injective
  change MvPolynomial.sumAlgEquiv S (Fin d) τ
      ((MvPolynomial.sumAlgEquiv S (Fin d) τ).symm (MvPolynomial.C p)) =
    MvPolynomial.sumAlgEquiv S (Fin d) τ (MvPolynomial.rename Sum.inr p)
  rw [AlgEquiv.apply_symm_apply]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem ideal_eq_inr_extension_of_inl_pderiv_stable (d : ℕ) (τ : Type*)
    (J : Ideal (MvPolynomial (Fin d ⊕ τ) R))
    (hD : ∀ i : Fin d, ∀ f ∈ J, MvPolynomial.pderiv (Sum.inl i) f ∈ J) :
    J = Ideal.map (MvPolynomial.rename (Sum.inr : τ → Fin d ⊕ τ)).toRingHom
      (Ideal.comap (MvPolynomial.rename (Sum.inr : τ → Fin d ⊕ τ)).toRingHom J) := by
  let e := MvPolynomial.sumAlgEquiv R (Fin d) τ
  let K := Ideal.comap e.symm.toRingHom J
  have hKD : ∀ i : Fin d, ∀ f ∈ K, MvPolynomial.pderiv i f ∈ K := by
    intro i f hf
    change e.symm (MvPolynomial.pderiv i f) ∈ J
    have heq : e.symm (MvPolynomial.pderiv i f) =
        MvPolynomial.pderiv (Sum.inl i) (e.symm f) := by
      apply e.injective
      simpa only [e, AlgEquiv.apply_symm_apply] using
        MvPolynomial.pderiv_sumAlgEquiv i (e.symm f)
    rw [heq]
    exact hD i (e.symm f) hf
  have hK := mvPolynomial_eq_map_C_comap_of_pderiv_stable d K hKD
  calc
    J = Ideal.map e.symm.toRingHom K :=
      (Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective J).symm
    _ = Ideal.map (MvPolynomial.rename (Sum.inr : τ → Fin d ⊕ τ)).toRingHom
        (Ideal.comap (MvPolynomial.rename (Sum.inr : τ → Fin d ⊕ τ)).toRingHom J) := by
      rw [hK, Ideal.map_map]
      change Ideal.map (e.symm.toRingHom.comp MvPolynomial.C)
        (Ideal.comap MvPolynomial.C (Ideal.comap e.symm.toRingHom J)) = _
      rw [Ideal.comap_comap, sumAlgEquiv_symm_comp_C]

/-- The original ideal equals its actual normal extension, assuming whole-ideal
tangent differential stability, including empty tangent and normal blocks. -/
theorem ideal_eq_normal_extension_of_tangent_pderiv_stable (d t : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + t)) ℂ))
    (hD : ∀ i : Fin d, ∀ f ∈ J, MvPolynomial.pderiv (i.castAdd t) f ∈ J) :
    J = Ideal.map
      (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d + t))).toRingHom
      (Ideal.comap
        (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d + t))).toRingHom J) := by
  let e := MvPolynomial.renameEquiv ℂ
    (finSumFinEquiv : Fin d ⊕ Fin t ≃ Fin (d + t))
  let K := Ideal.comap e.toRingHom J
  have hKD : ∀ i : Fin d, ∀ f ∈ K, MvPolynomial.pderiv (Sum.inl i) f ∈ K := by
    intro i f hf
    change MvPolynomial.rename finSumFinEquiv (MvPolynomial.pderiv (Sum.inl i) f) ∈ J
    rw [← MvPolynomial.pderiv_rename finSumFinEquiv.injective (Sum.inl i) f]
    exact hD i _ hf
  have hK := ideal_eq_inr_extension_of_inl_pderiv_stable d (Fin t) K hKD
  have hcomp : e.toRingHom.comp
        (MvPolynomial.rename (Sum.inr : Fin t → Fin d ⊕ Fin t)).toRingHom =
      (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d + t))).toRingHom := by
    ext a <;> simp [e, MvPolynomial.renameEquiv_apply]
  calc
    J = Ideal.map e.toRingHom K :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective J).symm
    _ = Ideal.map
        (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d + t))).toRingHom
        (Ideal.comap
          (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d + t))).toRingHom J) := by
      rw [hK, Ideal.map_map]
      change Ideal.map (e.toRingHom.comp
          (MvPolynomial.rename (Sum.inr : Fin t → Fin d ⊕ Fin t)).toRingHom)
        (Ideal.comap (MvPolynomial.rename (Sum.inr : Fin t → Fin d ⊕ Fin t)).toRingHom
          (Ideal.comap e.toRingHom J)) = _
      rw [Ideal.comap_comap, hcomp]

end
end Hironaka.HironakaDifferentialStableCylindricalIdeal
