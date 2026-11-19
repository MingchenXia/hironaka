import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Actual polynomial centre ideals descend from shift invariance

Source-first proof: `polynomial-translation-ideal-descent-20261101.tex`.
This is a coefficient producer for later actual padded-envelope history descent;
it does not itself supply or descend a resolution sequence.
-/

set_option autoImplicit false

namespace Hironaka.Resolution.Algebraic.PolynomialTranslationIdealDescent

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

private theorem coeff_taylor_eq_of_natDegree_le (f : R[X]) (n : ℕ)
    (h : f.natDegree ≤ n) : (taylor 1 f).coeff n = f.coeff n := by
  obtain hlt | heq := h.lt_or_eq
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using hlt), coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq, coeff_taylor_natDegree, coeff_natDegree]

private theorem shift_difference_coeff (f : R[X]) (n : ℕ) (hn : f.natDegree = n+1) :
    (taylor 1 f - f).coeff n = (n+1 : R) * f.leadingCoeff := by
  have hrem : f.eraseLead.natDegree ≤ n := by
    have h := f.eraseLead_natDegree_le
    simpa [hn] using h
  have hdecomp : taylor 1 f = taylor 1 f.eraseLead +
      C f.leadingCoeff * (X+1)^(n+1) := by
    conv_lhs => rw [← f.eraseLead_add_C_mul_X_pow]
    simp only [map_add, taylor_mul, taylor_C, taylor_X_pow, C_1, hn]
  rw [coeff_sub, hdecomp, coeff_add, coeff_taylor_eq_of_natDegree_le _ _ hrem,
    coeff_C_mul, coeff_X_add_one_pow, eraseLead_coeff_of_ne _ (by omega)]
  simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
  ring

private theorem shift_difference_natDegree_lt (f : R[X]) (hf : 0 < f.natDegree) :
    (taylor 1 f - f).natDegree < f.natDegree := by
  by_cases hg : taylor 1 f - f = 0
  · simpa [hg] using hf
  have hne : taylor 1 f ≠ 0 := by
    exact (taylor_eq_zero 1 f).not.mpr (ne_zero_of_natDegree_gt hf)
  apply (natDegree_lt_iff_degree_lt hg).mpr
  have h := degree_sub_lt_left (degree_taylor f 1) hne (leadingCoeff_taylor 1 f)
  simpa only [degree_taylor, degree_eq_natDegree (ne_zero_of_natDegree_gt hf)] using h

/-- Actual stability under the one-unit shift forces every constant
coefficient of every member of the SAME ideal into that ideal. -/
theorem coefficient_mem_of_shift_stable (K : Type*) [Field K] [CharZero K] [Algebra K R]
    (J : Ideal R[X]) (hshift : ∀ f ∈ J,taylor 1 f ∈ J)
    (f : R[X]) (hf : f ∈ J) (i : ℕ) : C (f.coeff i) ∈ J := by
  classical
  have hcoeff : ∀ n : ℕ, ∀ f : R[X], f.natDegree=n → f ∈ J →
      ∀ i : ℕ,C (f.coeff i) ∈ J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h m ih =>
      intro p hdeg hp i
      cases m with
      | zero =>
        by_cases hi : i=0
        · subst i
          have heq : p=C (p.coeff 0) := eq_C_of_natDegree_le_zero hdeg.le
          exact heq ▸ hp
        · have hpi : p.coeff i=0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
          simpa only [hpi, C_0] using J.zero_mem
      | succ n =>
        let g := taylor 1 p-p
        have hg : g ∈ J := J.sub_mem (hshift p hp) hp
        have hgn : g.natDegree < n+1 := by
          simpa only [hdeg] using shift_difference_natDegree_lt p (by omega)
        have hcg := ih g.natDegree hgn g rfl hg n
        change C ((taylor 1 p-p).coeff n) ∈ J at hcg
        rw [shift_difference_coeff p n hdeg] at hcg
        let c : R := algebraMap K R ((n+1 : K)⁻¹)
        have hnK : (n+1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have hcinv : c*(n+1 : R)=1 := by
          change algebraMap K R ((n+1 : K)⁻¹) * (n+1 : R)=1
          calc
            _ = algebraMap K R (((n+1 : K)⁻¹)*(n+1)) := by
              simp only [map_mul, map_add, map_natCast, map_one]
            _ = 1 := by rw [inv_mul_cancel₀ hnK, map_one]
        have hlc : C p.leadingCoeff ∈ J := by
          have h := J.mul_mem_left (C c) hcg
          have heq : C c * C ((n+1 : R)*p.leadingCoeff)=C p.leadingCoeff := by
            rw [← map_mul]
            congr 1
            rw [← mul_assoc, hcinv, one_mul]
          exact heq ▸ h
        by_cases hi : i=p.natDegree
        · simpa only [hi, coeff_natDegree] using hlc
        · have herase : p.eraseLead=p-C p.leadingCoeff*X^p.natDegree :=
            eq_sub_iff_add_eq.mpr p.eraseLead_add_C_mul_X_pow
          have he : p.eraseLead ∈ J := by
            rw [herase]
            exact J.sub_mem hp (J.mul_mem_right _ hlc)
          obtain hlt | hz := p.eraseLead_natDegree_lt_or_eraseLead_eq_zero
          · have h := ih p.eraseLead.natDegree (by simpa only [hdeg] using hlt)
              p.eraseLead rfl he i
            simpa only [eraseLead_coeff_of_ne i hi] using h
          · have hc : p.coeff i=0 := by
              rw [← eraseLead_coeff_of_ne i hi, hz, coeff_zero]
            simpa only [hc, C_0] using J.zero_mem
  exact hcoeff f.natDegree f rfl hf i

/-- The contracted base ideal is constructed from the actual shift-stable
ideal; no product-centre or coefficient certificate is supplied. -/
theorem ideal_eq_map_comap_of_shift_stable (K : Type*) [Field K] [CharZero K] [Algebra K R]
    (J : Ideal R[X]) (hshift : ∀ f ∈ J,taylor 1 f ∈ J) :
    J=Ideal.map (C : R →+* R[X]) (J.comap C) := by
  apply le_antisymm
  · intro f hf
    apply Ideal.mem_map_C_iff.mpr
    exact coefficient_mem_of_shift_stable K J hshift f hf
  · exact Ideal.map_comap_le

theorem mem_iff_coefficients_of_shift_stable (K : Type*) [Field K] [CharZero K] [Algebra K R]
    (J : Ideal R[X]) (hshift : ∀ f ∈ J,taylor 1 f ∈ J) (f : R[X]) :
    f ∈ J ↔ ∀ i : ℕ,C (f.coeff i) ∈ J := by
  constructor
  · exact fun hf => coefficient_mem_of_shift_stable K J hshift f hf
  · exact Ideal.polynomial_mem_ideal_of_coeff_mem_ideal J f

/-- The actual base ideal is also the actual pullback along the zero section,
so no independent base-centre ideal has to be selected. -/
theorem comap_eq_eval_zero_image_of_shift_stable (K : Type*)
    [Field K] [CharZero K] [Algebra K R]
    (J : Ideal R[X]) (hshift : ∀ f ∈ J,taylor 1 f ∈ J) :
    J.comap C=Ideal.map (evalRingHom (0 : R)) J := by
  apply le_antisymm
  · intro r hr
    have h := Ideal.mem_map_of_mem (evalRingHom (0 : R)) hr
    change (C r).eval 0 ∈ Ideal.map (evalRingHom (0 : R)) J at h
    simpa only [eval_C] using h
  · apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change C (f.eval 0) ∈ J
    rw [← coeff_zero_eq_eval_zero]
    exact coefficient_mem_of_shift_stable K J hshift f hf 0

/-- The same actual centre ideal is extended from its own zero-section image. -/
theorem ideal_eq_extension_of_zero_section_of_shift_stable (K : Type*)
    [Field K] [CharZero K] [Algebra K R]
    (J : Ideal R[X]) (hshift : ∀ f ∈ J,taylor 1 f ∈ J) :
    J=Ideal.map (C : R →+* R[X]) (Ideal.map (evalRingHom (0 : R)) J) := by
  rw [← comap_eq_eval_zero_image_of_shift_stable K J hshift]
  exact ideal_eq_map_comap_of_shift_stable K J hshift

end
end Hironaka.Resolution.Algebraic.PolynomialTranslationIdealDescent
