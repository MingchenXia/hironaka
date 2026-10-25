import DeJongAlterations.Algebra.CompletionIdealQuotient
import DeJongAlterations.Algebra.CompletionIntersectionRegularityCotangent
import DeJongAlterations.Algebra.CompletionIntersectionRegularityHeight

/-! Genuine completed-local intersection descent for the original finite family and its full original ideal. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionIntersectionRegularity

open CompletionRegularityBasics CompletionIntersectionRegularityCotangent

universe u v
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [IsRegularLocalRing (Completion R)]

/-- The original quotient is regular, derived from actual completed regularity and completed independence. -/
theorem isRegularLocalRing_original_quotient {ι : Type v} [Fintype ι] (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField (Completion R))
      (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i))) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) := by
  let : IsRegularLocalRing R := CompletionRegularity.isRegularLocalRing_of_completion R
  exact RegularQuotientFamily.isRegularLocalRing_quotient_family R t (independent_of_completed R t hli)

/-- Exact original quotient dimension drop, without an original independence or dimension certificate. -/
theorem ringKrullDim_original_quotient_add_card_eq {ι : Type v} [Fintype ι] (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField (Completion R))
      (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i))) :
    ringKrullDim (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) + Fintype.card ι = ringKrullDim R := by
  let : IsRegularLocalRing R := CompletionRegularity.isRegularLocalRing_of_completion R
  exact RegularQuotientFamily.ringKrullDim_quotient_family_add_card_eq R t (independent_of_completed R t hli)

/-- The full original intersection ideal has its genuine exact height. -/
theorem original_ideal_height {ι : Type v} [Fintype ι] (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField (Completion R))
      (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i))) :
    (Ideal.span (Set.range fun i ↦ (t i : R))).height = Fintype.card ι := by
  let : IsRegularLocalRing R := CompletionRegularity.isRegularLocalRing_of_completion R
  exact CompletionIntersectionRegularityHeight.span_original_family_height t (independent_of_completed R t hli)

/-- Actual original intersection regularity, dimension and ideal codimension, all from the literal completed data. -/
theorem original_intersection_regular_dimension_height {ι : Type v} [Fintype ι]
    (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField (Completion R))
      (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i))) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) + Fintype.card ι = ringKrullDim R ∧
      (Ideal.span (Set.range fun i ↦ (t i : R))).height = Fintype.card ι :=
  ⟨isRegularLocalRing_original_quotient R t hli, ringKrullDim_original_quotient_add_card_eq R t hli,
    original_ideal_height R t hli⟩

end DeJongAlterations.Algebra.CompletionIntersectionRegularity
