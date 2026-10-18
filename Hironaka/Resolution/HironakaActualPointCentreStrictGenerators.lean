/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticStrictGenerators

/-! Point centres internally satisfy the canonical centre-power condition for arbitrary original ideals. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointCentreStrictGenerators
noncomputable section
open HolGerm HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualAnalyticStrictGenerators
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalStrictGenerators

/-- Degree-first canonical reduced vertices lie in the WHOLE required point-centre powers automatically. -/
theorem actualReducedVertexSeries_mem_point_power (n : ℕ)
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices MonomialOrder.degLex J) :
    actualReducedVertexSeries MonomialOrder.degLex J a ∈
      actualFormalCoordinateIdeal n Set.univ ^ Finsupp.weight (actualCoordinateWeight Set.univ) a.val := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ _ _).mpr
  intro β hβ
  apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex J a β
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa [ofDegLex_toDegLex,Finsupp.degree_eq_sum,Finsupp.weight_eq_sum,actualCoordinateWeight] using hβ

/-- ONLY the original analytic ideal and actual point chart are inputs; no canonical centre-power certificate is supplied. -/
theorem exists_actual_point_normalized_member_generators (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ) :
    ∃ H : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n),
      actualAnalyticNormalizedMemberIdeal I Set.univ e b=Ideal.span (range H) ∧
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticNormalizedMemberIdeal I Set.univ e b)=
        actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
          Set.univ e (mem_univ e) b := by
  exact exists_actual_analytic_normalized_member_generators n I Set.univ e (mem_univ e) b
    (actualReducedVertexSeries_mem_point_power n _)

end
end Hironaka.HironakaActualPointCentreStrictGenerators
