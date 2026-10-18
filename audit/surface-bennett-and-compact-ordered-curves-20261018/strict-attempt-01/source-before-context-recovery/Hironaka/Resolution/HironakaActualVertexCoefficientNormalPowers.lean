/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalAxisDehomogenization
import Hironaka.Resolution.HironakaActualCoefficientAnalyticBlowup

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualVertexCoefficientNormalPowers
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm GermIdealOrder OkaRelationSheaf
  HironakaActualFiniteCoefficientIdeals HironakaActualFormalInitialDiagram HironakaHolomorphicPointJets
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualCoefficientReducedStrictGenerators
  HironakaActualCoefficientAnalyticBlowup HironakaActualAnalyticVertexCoefficientData
  HironakaActualLocalCoefficientStrictGenerators HironakaActualAnalyticFormalNormalPowers
  HironakaActualOriginalFormalTaylor HironakaActualFormalCoordinatePowerDivision
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualNormalHomogeneousComponents HironakaActualNormalAxisDehomogenization
  HironakaActualAxisContraction HironakaActualNormalScalingRays

/-- The literal zero-middle presentation centre is exactly the original last normal block. -/
theorem actualCoefficientCentreVariables_zero_middle (d t : ℕ) :
    actualCoefficientCentreVariables d 0 t=actualTangentCentreVariables d t := by
  rw [actualCoefficientCentreVariables,actualPresentationCentreVariables_eq_tail,
    actualTangentCentreVariables_eq_tail]
  rfl

/-- Actual original presentation and normal vertex weights agree without changing the exponent. -/
theorem actualCoefficientCentreVertexWeight_zero_middle (d t : ℕ) (a : Fin (d+t) →₀ ℕ) :
    actualCoefficientCentreVertexWeight d 0 t a=
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a := by
  rw [actualCoefficientCentreVertexWeight,actualCoefficientCentreVariables_zero_middle]

/-- ORIGINAL local coefficient cosupport gives every SAME original analytic vertex its ENTIRE normal power. -/
theorem actualVertexCoefficientData_generator_mem_normal_pow (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hcosupp : ∀ (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) (γ : Fin t →₀ ℕ),
      actualNormalDegree γ<actualCoefficientCentreVertexWeight d 0 t a.val →
      P.domain ∩ complexCoordinatePlane (d+0) d ⊆
        cosupport (d+0) univ (actualPrincipalCoefficientIdeal (d+0) (P.coefficient a γ))
          (actualCoefficientCentreVertexWeight d 0 t a.val-actualNormalDegree γ))
    (a : HironakaActualFormalInitialDiagram.actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    P.generator a ∈ normalIdeal d t ^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  have hF := mem_actualPresentationCentre_power_of_local_coefficient_cosupport d 0 t
    (actualCoefficientCentreVertexWeight d 0 t a.val)
    (actualUnshiftedTaylorAlgHom (d+t) (P.generator a))
    P.domain P.isOpen_domain P.zero_mem_domain (P.coefficient a) (P.holomorphic a)
    (fun γ => actualPrincipalCoefficientIdeal (d+0) (P.coefficient a γ))
    (P.coherent a) (P.coefficient_member a) (hcosupp a) (fun γ _ => P.coefficient_eq a γ)
  change actualUnshiftedTaylorAlgHom (d+t) (P.generator a) ∈
    actualFormalCoordinateIdeal (d+t) (actualCoefficientCentreVariables d 0 t) ^
      actualCoefficientCentreVertexWeight d 0 t a.val at hF
  rw [actualCoefficientCentreVariables_zero_middle,actualCoefficientCentreVertexWeight_zero_middle] at hF
  exact (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (P.generator a)).mpr hF

/-- The SAME canonical symbols lie in the entire zero-axis normalized image using ONLY original coefficient cosupport. -/
theorem actualVertexCoefficientData_dehomogenizedFamily_le_axis_normalized_image (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hcosupp : ∀ (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) (γ : Fin t →₀ ℕ),
      actualNormalDegree γ<actualCoefficientCentreVertexWeight d 0 t a.val →
      P.domain ∩ complexCoordinatePlane (d+0) d ⊆
        cosupport (d+0) univ (actualPrincipalCoefficientIdeal (d+0) (P.coefficient a γ))
          (actualCoefficientCentreVertexWeight d 0 t a.val-actualNormalDegree γ))
    (j : Fin t) (b : Fin (d+t) → ℂ) :
    actualDehomogenizedNormalFamilyIdeal d t
      (fun a => actualNormalHomogeneousPolynomial d t
        (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) (P.generator a)) j b ≤
      Ideal.map (actualAxisContractionGerm (j.natAdd d) 0).toRingHom
        (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) := by
  exact actualDehomogenizedNormalFamilyIdeal_le_axis_normalized_image d t I P.generator
    (fun a => Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    P.member (actualVertexCoefficientData_generator_mem_normal_pow d t I P hcosupp) j b

/-- No numeric HS or normal-power input: original coefficient cosupport yields ALL original translated-family bounds. -/
theorem hilbertSamuelValue_actualVertexCoefficientData_normalized_le_translated (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hcosupp : ∀ (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) (γ : Fin t →₀ ℕ),
      actualNormalDegree γ<actualCoefficientCentreVertexWeight d 0 t a.val →
      P.domain ∩ complexCoordinatePlane (d+0) d ⊆
        cosupport (d+0) univ (actualPrincipalCoefficientIdeal (d+0) (P.coefficient a γ))
          (actualCoefficientCentreVertexWeight d 0 t a.val-actualNormalDegree γ))
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) ℓ ≤
      hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t
        (fun a => actualNormalHomogeneousPolynomial d t
          (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) (P.generator a))
        (fun i => if i=j then 1 else b (i.natAdd d))) ℓ := by
  exact hilbertSamuelValue_actual_normal_normalized_le_translated d t I P.generator
    (fun a => Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    P.member (actualVertexCoefficientData_generator_mem_normal_pow d t I P hcosupp) j b ℓ

end
end Hironaka.HironakaActualVertexCoefficientNormalPowers
