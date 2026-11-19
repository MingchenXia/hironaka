import Hironaka.Resolution.HironakaG8MarkTwoCoefficientClass
import Hironaka.Resolution.HironakaG8InitialCommonIdealMaximum

/-! The original first value can forget all quadratic generator counts. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG8QuadraticInitialTieCriterion
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong HironakaG8MarkTwoCoefficientClass HironakaG8MarkTwoFullCoefficient
  HironakaG8InitialCommonIdealMaximum HironakaSharpOriginalProductTraceOrder
  NonmonomialOrderLocal GermIdealOrder RestrictedIdealExtension DerivativeIdeal IdealWeightPowers

variable {n : ℕ} {X : CMfd.{0} (n+1)}

abbrev fullRecord (I : GermIdeal (n+1) X) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ, [], I, d⟩

/-- Two whole analytic ideals of ordinary order two have the same original
mark-one initial value whenever their exact derivative-square recodings
agree. The naive first comparison by the original Hilbert–Samuel profile
can still distinguish the generator ranks. -/
theorem mark_one_initial_value_eq_of_quadratic_recoding
    (I J : GermIdeal (n+1) X)
    (hI : IsInvDomain (n+1) (fullRecord I 2)) (hJ : IsInvDomain (n+1) (fullRecord J 2))
    (x : X) (hxI : x ∈ (fullRecord I 2).cosupp) (hxJ : x ∈ (fullRecord J 2).cosupp)
    (hOrdI : nmOrd (fullRecord I 1) x = 2) (hOrdJ : nmOrd (fullRecord J 1) x = 2)
    (hEq : sumIdeal I (idealPow (derivIdeal I) 2) = sumIdeal J (idealPow (derivIdeal J) 2)) :
    (canonicalInvariant (n+1)).inv (fullRecord I 1) (.refl : BlowupTower X X) x =
      (canonicalInvariant (n+1)).inv (fullRecord J 1) (.refl : BlowupTower X X) x := by
  have hC : coeffMarkedAlong (fullRecord I 2) = coeffMarkedAlong (fullRecord J 2) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪 := coeffMarkedAlong (fullRecord I 2)) (𝔫 := coeffMarkedAlong (fullRecord J 2))
      rfl rfl ?_ rfl
    rw [mark_two_coefficient_ideal (fullRecord I 2) hI.isWellFormed.isCoherent rfl rfl,
      mark_two_coefficient_ideal (fullRecord J 2) hJ.isWellFormed.isCoherent rfl rfl]
    exact hEq
  rw [initial_value_eq_of_common_ideal I (d := 1) (e := 2) (o := 2)
      (by decide) le_rfl (by decide) hOrdI,
    initial_value_eq_of_common_ideal J (d := 1) (e := 2) (o := 2)
      (by decide) le_rfl (by decide) hOrdJ]
  rw [← mark_two_double_coefficient_original_initial_value (fullRecord I 2) hI rfl rfl rfl x hxI,
    ← mark_two_double_coefficient_original_initial_value (fullRecord J 2) hJ rfl rfl rfl x hxJ,
    mark_two_double_coefficient_record_eq (fullRecord I 2) hI.isWellFormed.isCoherent rfl rfl,
    mark_two_double_coefficient_record_eq (fullRecord J 2) hJ.isWellFormed.isCoherent rfl rfl, hC]

end
end Hironaka.HironakaG8QuadraticInitialTieCriterion
