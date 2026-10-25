/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Algebra.RegularLocalDomainPrimeFamily
import DeJongAlterations.Algebra.RegularQuotient
import DeJongAlterations.Algebra.RegularLocalDomainPrincipal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square

/-!
# Regular local rings are actual domains

Cotangent parameters yield infinitely many distinct prime perturbations.
Together with actual lower-dimensional parameter quotients and Krull intersection,
this gives a direct induction without an associated-graded presentation certificate.
-/

open IsLocalRing

set_option autoImplicit false

namespace DeJongAlterations.Algebra.RegularLocalDomain

noncomputable section

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Two independent cotangent directions have actual lifts in the maximal ideal. -/
theorem exists_two_parameters [IsNoetherianRing R]
    (hdim : 2 ≤ Module.finrank (ResidueField R) (CotangentSpace R)) :
    ∃ x y : maximalIdeal R,
      (maximalIdeal R).toCotangent x ≠ 0 ∧
      ∀ a : ResidueField R, (maximalIdeal R).toCotangent y ≠
        a • (maximalIdeal R).toCotangent x := by
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  let i : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) := ⟨0, by omega⟩
  let j : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have h' := congrArg Fin.val h; dsimp [i, j] at h'; omega
  obtain ⟨x, hx⟩ := (maximalIdeal R).toCotangent_surjective (b i)
  obtain ⟨y, hy⟩ := (maximalIdeal R).toCotangent_surjective (b j)
  refine ⟨x, y, ?_, ?_⟩
  · rw [hx]
    exact b.ne_zero i
  · rw [hx, hy]
    intro a h
    have h' := congrArg (fun v ↦ b.repr v j) h
    simp [hij.symm] at h'

/-- Infinitely many actual parameters share the first cotangent direction. -/
def perturbation (x y : maximalIdeal R) (n : ℕ) : R :=
  (x : R) + (y : R) ^ (n + 2)

theorem perturbation_mem (x y : maximalIdeal R) (n : ℕ) :
    perturbation R x y n ∈ maximalIdeal R := by
  apply (maximalIdeal R).add_mem x.property
  rw [pow_succ]
  exact (maximalIdeal R).mul_mem_left _ y.property

/-- The added higher power has genuinely zero cotangent class. -/
theorem perturbation_toCotangent (x y : maximalIdeal R) (n : ℕ) :
    (maximalIdeal R).toCotangent ⟨perturbation R x y n, perturbation_mem R x y n⟩ =
      (maximalIdeal R).toCotangent x := by
  have hy2 : (y : R) ^ (n + 2) ∈ maximalIdeal R ^ 2 := by
    rw [pow_add]
    exact (maximalIdeal R ^ 2).mul_mem_left _ (Ideal.pow_mem_pow y.property 2)
  apply (maximalIdeal R).toCotangent_eq.mpr
  simpa [perturbation] using hy2

/-- Every actual perturbation remains a nonzero cotangent parameter. -/
theorem perturbation_not_mem_sq (x y : maximalIdeal R)
    (hx : (maximalIdeal R).toCotangent x ≠ 0) (n : ℕ) :
    perturbation R x y n ∉ maximalIdeal R ^ 2 := by
  intro h
  apply hx
  rw [← perturbation_toCotangent R x y n]
  exact ((maximalIdeal R).toCotangent_eq_zero _).mpr h

/-- The second cotangent direction survives in each actual parameter quotient. -/
theorem second_not_mem_perturbation (x y : maximalIdeal R)
    (hy : ∀ a : ResidueField R, (maximalIdeal R).toCotangent y ≠
      a • (maximalIdeal R).toCotangent x) (n : ℕ) :
    (y : R) ∉ Ideal.span ({perturbation R x y n} : Set R) := by
  intro h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp h
  have heq : y = a • (⟨perturbation R x y n, perturbation_mem R x y n⟩ : maximalIdeal R) :=
    Subtype.ext (by simpa only [Submodule.coe_smul_of_tower, smul_eq_mul, mul_comm] using ha)
  have hc := congrArg (maximalIdeal R).toCotangent heq
  rw [map_smul, perturbation_toCotangent] at hc
  apply hy (algebraMap R (ResidueField R) a)
  exact hc.trans (IsScalarTower.algebraMap_smul (ResidueField R) a _).symm

private theorem not_both_mem_perturbations (x y : maximalIdeal R)
    (P : Ideal R) (hP : P.IsPrime) (hPm : P ≤ maximalIdeal R) (hyP : (y : R) ∉ P)
    {n m : ℕ} (hnm : n < m) :
    ¬ (perturbation R x y n ∈ P ∧ perturbation R x y m ∈ P) := by
  rintro ⟨hn, hm⟩
  have heq : perturbation R x y n - perturbation R x y m =
      (y : R) ^ (n + 2) * (1 - (y : R) ^ (m - n)) := by
    unfold perturbation
    rw [show m + 2 = (n + 2) + (m - n) by omega, pow_add]
    ring
  have hprod : (y : R) ^ (n + 2) * (1 - (y : R) ^ (m - n)) ∈ P :=
    heq ▸ P.sub_mem hn hm
  rcases hP.mem_or_mem hprod with hpow | hsecond
  · exact hyP (hP.mem_of_pow_mem (n + 2) hpow)
  · have hpow : (y : R) ^ (m - n) ∈ maximalIdeal R :=
      (maximalIdeal R).pow_mem_of_mem y.property _ (Nat.sub_pos_of_lt hnm)
    have hone : (1 : R) ∈ maximalIdeal R := by
      simpa only [sub_add_cancel] using (maximalIdeal R).add_mem (hPm hsecond) hpow
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- Actual prime perturbations are pairwise noncontaining, over arbitrary residue fields. -/
theorem perturbation_pairwise_not_mem (x y : maximalIdeal R)
    (hy : ∀ a : ResidueField R, (maximalIdeal R).toCotangent y ≠
      a • (maximalIdeal R).toCotangent x)
    (hprime : ∀ n, (Ideal.span ({perturbation R x y n} : Set R)).IsPrime)
    (n m : ℕ) (hnm : n ≠ m) :
    perturbation R x y n ∉ Ideal.span ({perturbation R x y m} : Set R) := by
  intro hn
  let P := Ideal.span ({perturbation R x y m} : Set R)
  have hPm : P ≤ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr (perturbation_mem R x y m)
  have hyP : (y : R) ∉ P := second_not_mem_perturbation R x y hy m
  have hm : perturbation R x y m ∈ P := Ideal.mem_span_singleton_self _
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact not_both_mem_perturbations R x y P (hprime m) hPm hyP hlt ⟨hn, hm⟩
  · exact not_both_mem_perturbations R x y P (hprime m) hPm hyP hgt ⟨hm, hn⟩

end

noncomputable section

universe u

private theorem isDomain_of_spanFinrank (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R _ _ hrank
    have hregular : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
      (isRegularLocalRing_iff R).mp inferInstance
    by_cases hn0 : n = 0
    · have hm : maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot
          (maximalIdeal R).fg_of_isNoetherianRing).mp (hrank.trans hn0)
      let := ((isField_iff_maximalIdeal_eq (R := R)).mpr hm).toField
      infer_instance
    by_cases hn1 : n = 1
    · have hpos : 0 < ringKrullDim R := by rw [← hregular, hrank, hn1]; norm_num
      obtain ⟨t, ht, ht2⟩ := SetLike.exists_of_lt (maximalIdeal_sq_lt_of_ringKrullDim_ne_zero (ne_of_gt hpos))
      obtain ⟨N, x, hgen, hN⟩ := RegularQuotient.exists_parameter_generators R t ht ht2
      have hzero : N = 0 := by omega
      subst N
      have hm : maximalIdeal R = Ideal.span ({t} : Set R) := by simpa using hgen.symm
      exact RegularLocalDomainPrincipal.isDomain_of_principal_maximalIdeal_of_pos_dim t hm hpos
    have htwo : 2 ≤ n := by omega
    have hdim : 2 ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R, hrank]
      exact htwo
    obtain ⟨x, y, hx, hy⟩ := exists_two_parameters R hdim
    have hprime (j : ℕ) : (Ideal.span ({perturbation R x y j} : Set R)).IsPrime := by
      let t := perturbation R x y j
      have ht : t ∈ maximalIdeal R := perturbation_mem R x y j
      have ht2 : t ∉ maximalIdeal R ^ 2 := perturbation_not_mem_sq R x y hx j
      let C := R ⧸ Ideal.span ({t} : Set R)
      let : IsRegularLocalRing C := RegularQuotient.isRegularLocalRing_quotient_parameter R t ht ht2
      have hCregular : ((maximalIdeal C).spanFinrank : WithBot ℕ∞) = ringKrullDim C :=
        (isRegularLocalRing_iff C).mp inferInstance
      have hdrop := RegularQuotient.ringKrullDim_quotient_parameter_add_one_eq R t ht ht2
      change ringKrullDim C + 1 = ringKrullDim R at hdrop
      rw [← hCregular, ← hregular, hrank] at hdrop
      have hnat : (maximalIdeal C).spanFinrank + 1 = n := by exact_mod_cast hdrop
      let : IsDomain C := ih (maximalIdeal C).spanFinrank (by omega) C rfl
      exact (Ideal.Quotient.isDomain_iff_prime _).mp (inferInstance : IsDomain C)
    exact RegularLocalDomainPrimeFamily.isDomain_of_infinite_principal_primes
      (perturbation R x y) (perturbation_mem R x y) hprime
      (perturbation_pairwise_not_mem R x y hy hprime)

/-- Every actual native Noetherian regular local ring is an integral domain. -/
theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_spanFinrank (maximalIdeal R).spanFinrank R rfl

end

end DeJongAlterations.Algebra.RegularLocalDomain
