/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualVertexCoefficientNormalPowers
import Hironaka.Resolution.HironakaActualTranslatedNormalVertexHS
import Hironaka.Resolution.HironakaActualNormalBlowupExceptionalLocus

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCoefficientCentreBennett
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm GermIdealOrder
  HironakaActualAnalyticVertexCoefficientData HironakaActualFormalInitialDiagram
  HironakaActualFormalCoordinatePowerDivision HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaActualCoefficientPresentationCentrePower HironakaActualCoefficientReducedStrictGenerators
  HironakaActualFiniteCoefficientIdeals HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualVertexCoefficientNormalPowers HironakaActualTranslatedNormalVertexHS
  HironakaActualNormalBlowupExceptionalLocus HironakaActualPointGeometricBennett
  HironakaRelativeNormalDeformationInitialRelations

/-- Only ORIGINAL coefficient cosupport, not an HS/normal-power certificate, gives the actual normalized Bennett bound. -/
theorem hilbertSamuelValue_actual_coefficient_centre_normalized_le (d t : ℕ)
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
      hilbertSamuelValue I ℓ := by
  apply (hilbertSamuelValue_actualVertexCoefficientData_normalized_le_translated d t I P hcosupp j b ℓ).trans
  exact hilbertSamuelValue_actualTranslatedNormalVertexIdeal_le d t I P _ ℓ

section Geometric
variable (d t : ℕ) (W : Set (ComplexModel (d+t)))
  (P : ActualAnalyticVertexCoefficientData d 0 t (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)))
  (hcosupp : ∀ (a : actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)))) (γ : Fin t →₀ ℕ),
    actualNormalDegree γ<actualCoefficientCentreVertexWeight d 0 t a.val →
    P.domain ∩ complexCoordinatePlane (d+0) d ⊆
      cosupport (d+0) univ (actualPrincipalCoefficientIdeal (d+0) (P.coefficient a γ))
        (actualCoefficientCentreVertexWeight d 0 t a.val-actualNormalDegree γ))
include hcosupp

/-- The actual original geometric strict transform has EVERY intrinsic HS order bounded when normal codimension is at least two. -/
theorem hilbertSamuelAt_actual_coefficient_centre_strict_le_of_two_le (ht : 2 ≤ t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) 0 ℓ := by
  apply (hilbertSamuelAt_actual_normal_strict_le_normalized d t ht j b W ℓ).trans
  rw [hilbertSamuelAt_model_zero]
  exact hilbertSamuelValue_actual_coefficient_centre_normalized_le d t _ P hcosupp j b ℓ

/-- The true identity/divisor case is treated by the original geometric closure, retaining all ambient tangent coordinates. -/
theorem hilbertSamuelAt_actual_coefficient_centre_strict_le
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) 0 ℓ := by
  by_cases ht : t=1
  · subst t
    exact (hilbertSamuelAt_actual_normal_blowup_one d j b W ℓ).le
  · have hj := j.isLt
    exact hilbertSamuelAt_actual_coefficient_centre_strict_le_of_two_le d t W P hcosupp (by omega) j b ℓ

end Geometric
end
end Hironaka.HironakaActualCoefficientCentreBennett
