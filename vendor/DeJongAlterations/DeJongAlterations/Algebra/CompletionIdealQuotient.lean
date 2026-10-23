import DeJongAlterations.Algebra.CompletionRegularity

/-! Actual arbitrary original-ideal completion quotients with quotient local structure derived internally. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionIdealQuotient

open CompletionRegularityBasics CompletionRegularityQuotient

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The actual quotient is nontrivial, derived from containment in the original maximal ideal. -/
theorem quotientNontrivial (J : Ideal R) (hJ : J ≤ maximalIdeal R) : Nontrivial (R ⧸ J) :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)

/-- The actual quotient local structure is derived from the original surjective quotient map. -/
theorem quotientLocalRing (J : Ideal R) (hJ : J ≤ maximalIdeal R) : IsLocalRing (R ⧸ J) := by
  let : Nontrivial (R ⧸ J) := quotientNontrivial J hJ
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

variable [IsNoetherianRing R]

/-- The entire original ideal quotient has its literal maximal-adic completion, with no supplied comparison. -/
def completionQuotientEquiv (J : Ideal R) (hJ : J ≤ maximalIdeal R) :
    letI := quotientLocalRing J hJ
    Completion (R ⧸ J) ≃+* (Completion R ⧸ J.map (algebraMap R (Completion R))) := by
  let := quotientLocalRing J hJ
  exact (quotientCompletionEquiv J).symm

/-- Exact original coefficient and canonical completion formula for the full original ideal. -/
theorem completionQuotientEquiv_coefficient (J : Ideal R) (hJ : J ≤ maximalIdeal R) (a : R) :
    letI := quotientLocalRing J hJ
    completionQuotientEquiv J hJ
      (AdicCompletion.of (maximalIdeal (R ⧸ J)) (R ⧸ J) (Ideal.Quotient.mk J a)) =
        Ideal.Quotient.mk _ (AdicCompletion.of (maximalIdeal R) R a) := by
  let := quotientLocalRing J hJ
  exact (quotientCompletionEquiv J).symm_apply_eq.mpr
    (quotientCompletionEquiv_coefficient J a).symm

/-- The original quotient is regular if its actual full extended-ideal quotient in completion is regular. -/
theorem isRegularLocalRing_quotient_of_completion_quotient
    (J : Ideal R)
    [IsRegularLocalRing (Completion R ⧸ J.map (algebraMap R (Completion R)))] :
    IsRegularLocalRing (R ⧸ J) := by
  have hmap : J.map (algebraMap R (Completion R)) ≠ ⊤ :=
    Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hproper : J ≠ ⊤ := by
    intro h
    apply hmap
    rw [h, Ideal.map_top]
  have hJ : J ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hproper
  let := quotientLocalRing J hJ
  let : IsRegularLocalRing (Completion (R ⧸ J)) :=
    IsRegularLocalRing.of_ringEquiv (completionQuotientEquiv J hJ).symm
  exact CompletionRegularity.isRegularLocalRing_of_completion (R ⧸ J)

end DeJongAlterations.Algebra.CompletionIdealQuotient
