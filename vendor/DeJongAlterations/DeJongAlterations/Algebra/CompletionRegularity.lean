import DeJongAlterations.Algebra.CompletionRegularityQuotient
import DeJongAlterations.Algebra.RegularQuotient
import DeJongAlterations.Algebra.RegularLocalDomain
import Mathlib.RingTheory.KrullDimension.Regular

/-! Regularity reflects from the literal maximal-adic completion of the original Noetherian local ring. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionRegularity

open CompletionRegularityBasics CompletionRegularityQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Induction on the actual original embedding dimension, retaining the original quotient and completion map. -/
private theorem reflection_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      (maximalIdeal R).spanFinrank = n →
      IsRegularLocalRing (Completion R) → IsRegularLocalRing R := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R _ _ _ hrank hcompletion
    let : IsRegularLocalRing (Completion R) := hcompletion
    by_cases hf : IsField R
    · let := hf.toField
      infer_instance
    obtain ⟨t, ht, ht2⟩ := SetLike.exists_of_lt ((maximalIdeal_sq_lt_maximalIdeal R).mpr hf)
    let c := algebraMap R (Completion R) t
    have hc : c ∈ maximalIdeal (Completion R) := by
      change t ∈ (maximalIdeal (Completion R)).comap (algebraMap R (Completion R))
      rw [IsLocalRing.maximalIdeal_comap]
      exact ht
    have hc2 : c ∉ maximalIdeal (Completion R) ^ 2 := by
      intro h
      exact ht2 ((mem_maximalIdeal_sq_iff R t).mp h)
    let : IsRegularLocalRing (Completion R ⧸ Ideal.span {c}) :=
      RegularQuotient.isRegularLocalRing_quotient_parameter (Completion R) c hc hc2
    let J : Ideal R := Ideal.span {t}
    let Q := R ⧸ J
    have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      (Ideal.span_le.mpr (by simpa using ht))
    let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJ
    let : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let e : (Completion R ⧸ Ideal.span {c}) ≃+* Completion Q := principalQuotientCompletionEquiv t
    let : IsRegularLocalRing (Completion Q) := IsRegularLocalRing.of_ringEquiv e
    have hdim : ringKrullDim (Completion Q) + 1 = ringKrullDim (Completion R) := by
      rw [← ringKrullDim_eq_of_ringEquiv e]
      exact RegularQuotient.ringKrullDim_quotient_parameter_add_one_eq (Completion R) c hc hc2
    have hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim (Completion R) := by
      rw [← AdicCompletion.spanFinrank_maximalIdeal_eq (R := R)]
      exact (isRegularLocalRing_iff (Completion R)).mp inferInstance
    have hQ : ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) = ringKrullDim (Completion Q) := by
      rw [← AdicCompletion.spanFinrank_maximalIdeal_eq (R := Q)]
      exact (isRegularLocalRing_iff (Completion Q)).mp inferInstance
    have hranks : (maximalIdeal Q).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
      have h : ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) + 1 =
          ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by rw [hQ, hR]; exact hdim
      exact_mod_cast h
    have hlt : (maximalIdeal Q).spanFinrank < n := by omega
    let : IsRegularLocalRing Q := ih _ hlt Q rfl inferInstance
    let : IsDomain (Completion R) := RegularLocalDomain.isDomain_of_isRegularLocalRing _
    let : IsDomain R := (algebraMap_injective R).isDomain
    have ht0 : t ≠ 0 := by
      intro hz
      apply ht2
      rw [hz]
      exact Ideal.zero_mem _
    have htreg : t ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ht0
    have hdR : ringKrullDim Q + 1 = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors htreg ht
    apply (isRegularLocalRing_iff R).mpr
    calc
      ((maximalIdeal R).spanFinrank : WithBot ℕ∞) =
          ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) + 1 := by exact_mod_cast hranks.symm
      _ = ringKrullDim Q + 1 := by rw [(isRegularLocalRing_iff Q).mp inferInstance]
      _ = ringKrullDim R := hdR

/-- Genuine completed-local regularity implies native regularity of the original Noetherian local ring. -/
theorem isRegularLocalRing_of_completion (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsRegularLocalRing (Completion R)] : IsRegularLocalRing R :=
  reflection_aux (maximalIdeal R).spanFinrank R rfl inferInstance

end DeJongAlterations.Algebra.CompletionRegularity
