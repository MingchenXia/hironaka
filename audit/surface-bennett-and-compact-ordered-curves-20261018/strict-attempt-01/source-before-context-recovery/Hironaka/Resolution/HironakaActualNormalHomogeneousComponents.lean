/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Resolution.HironakaActualWeightedVertexHS
import Hironaka.Resolution.HironakaActualAnalyticVertexCoefficientData
import Hironaka.Resolution.HironakaActualUnshiftedInitialHSTransfer
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalHomogeneousComponents
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaActualWeightedVertexHS HironakaActualAnalyticVertexCoefficientData
  HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
  HironakaActualUnshiftedInitialHSTransfer HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets

/-- The true finite normal homogeneous polynomial, with entire original analytic tangent germs as coefficients. -/
def actualNormalHomogeneousPolynomial (d t q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  MvPolynomial.homogeneousComponent q (actualNormalTaylorPolynomial d t (q+1) g)

/-- Each actual coefficient is the original stable tangent coefficient at the specified normal degree. -/
theorem actualNormalHomogeneousPolynomial_coefficient (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    MvPolynomial.coeff γ (actualNormalHomogeneousPolynomial d t q g)=
      if normalExponentDegree γ=q then actualNormalAnalyticCoefficientGerm d t g γ else 0 := by
  rw [actualNormalHomogeneousPolynomial,MvPolynomial.coeff_homogeneousComponent]
  have hd : Finsupp.degree γ=normalExponentDegree γ := by
    simp [Finsupp.degree_eq_sum,normalExponentDegree]
  rw [hd]
  split_ifs with hγ
  · exact actualNormalTaylorPolynomial_coefficient_eq_germ d t (q+1) g γ (by omega)
  · rfl

/-- Genuine normal homogeneity holds in the finite polynomial ring over the entire original tangent germ ring. -/
theorem actualNormalHomogeneousPolynomial_isHomogeneous (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    (actualNormalHomogeneousPolynomial d t q g).IsHomogeneous q :=
  MvPolynomial.homogeneousComponent_isHomogeneous _ _

/-- Its entire actual original Taylor expansion is the literal normal-weight component, with zero tangent weights. -/
theorem actualTaylor_normalHomogeneousPolynomial (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t (actualNormalHomogeneousPolynomial d t q g))=
      actualWeightedComponent (actualCoordinateWeight (actualTangentCentreVariables d t)) q
        (actualUnshiftedTaylorAlgHom (d+t) g) := by
  apply MvPowerSeries.ext
  intro a
  let β := actualTangentExponent a
  let γ := actualNormalExponent a
  have he : actualJoinedExponent β γ=a := actualJoinedExponent_split a
  rw [← he,actualWeightedComponent_coefficient,actualJoinedExponent_normal_weight]
  have hp := congrArg (MvPowerSeries.coeff β) (actualFormalNormalCoefficient_normalPolynomialEval d t
    (actualNormalHomogeneousPolynomial d t q g) γ)
  change MvPowerSeries.coeff (actualJoinedExponent β γ)
    (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t (actualNormalHomogeneousPolynomial d t q g)))=
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom d
        (MvPolynomial.coeff γ (actualNormalHomogeneousPolynomial d t q g))) at hp
  rw [hp,actualNormalHomogeneousPolynomial_coefficient]
  split_ifs with hγ
  · have hc := congrArg (MvPowerSeries.coeff β) (actualFormalNormalCoefficient_actualTaylor d t g γ)
    exact hc.symm
  · simp only [map_zero]

/-- The whole original analytic ideal of the actual normal symbols of genuine analytic monic vertices. -/
def actualAnalyticNormalVertexComponentIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I) :
    Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) =>
    normalPolynomialEval d t (actualNormalHomogeneousPolynomial d t
      (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) (P.generator a)))

/-- The entire image ideal is precisely the span of the unchanged actual vertex-weight components. -/
theorem actualAnalyticNormalVertexComponentIdeal_formal_extension (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I) :
    Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualAnalyticNormalVertexComponentIdeal d t I P)=
      Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) =>
      actualWeightedComponent (actualCoordinateWeight (actualTangentCentreVariables d t))
        (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
        (actualUnshiftedTaylorAlgHom (d+t) (P.generator a))) := by
  rw [actualAnalyticNormalVertexComponentIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact actualTaylor_normalHomogeneousPolynomial d t _ (P.generator a)

/-- ONLY the original analytic ideal internally supplies the entire analytic-symbol HS bound at every order. -/
theorem exists_actualAnalyticNormalVertexComponentIdeal_hs_le (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I, ∀ ℓ : ℕ,
      hilbertSamuelValue (actualAnalyticNormalVertexComponentIdeal d t I P) ℓ ≤ hilbertSamuelValue I ℓ := by
  obtain ⟨P⟩ := nonempty_actualAnalyticVertexCoefficientData d 0 t I
  refine ⟨P,?_⟩
  intro ℓ
  let K := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom (d+t) (P.generator a)
      mem := fun a => Ideal.mem_map_of_mem _ (P.member a)
      monic := P.monic
      lower := fun a β hβ => coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _
        (P.nonzero a) β (by rwa [P.initial a]) }
  rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension (d+t) (actualAnalyticNormalVertexComponentIdeal d t I P),
    hilbertSamuelValue_eq_actual_unshifted_formal_extension (d+t) I,
    actualAnalyticNormalVertexComponentIdeal_formal_extension]
  change HironakaActualOriginalFormalHSTransfer.genuineFormalHilbertSamuelValue (d+t)
    (actualWeightedVertexIdeal MonomialOrder.degLex K B (actualCoordinateWeight (actualTangentCentreVariables d t))) ℓ ≤ _
  exact genuineFormalHilbertSamuelValue_weightedVertex_le K B _ ℓ

end
end Hironaka.HironakaActualNormalHomogeneousComponents
