/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalHomogeneousComponents
import Hironaka.Resolution.HironakaActualTranslatedNormalFamilyHS

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTranslatedNormalVertexHS
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualNormalHomogeneousComponents HironakaActualNormalScalingRays
  HironakaActualTranslatedNormalFamilyHS HironakaActualWeightedVertexHS
  HironakaActualAnalyticVertexCoefficientData HironakaActualFormalInitialDiagram
  HironakaActualReducedBasisDivision HironakaActualUnshiftedInitialHSTransfer
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision

/-- Translation by zero evaluates every genuine finite polynomial by the unchanged actual normal coordinates. -/
theorem actualTranslatedNormalPolynomialEval_zero (d t : ℕ)
    (Q : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualTranslatedNormalPolynomialEval d t 0 Q=normalPolynomialEval d t Q := by
  simp only [actualTranslatedNormalPolynomialEval,Pi.zero_apply,map_zero,add_zero]
  rfl

/-- The whole translated ideal uses the SAME original analytic vertices and their own actual normal weights. -/
def actualTranslatedNormalVertexIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (p : Fin t → ℂ) : Ideal (HolGerm (ComplexModel (d+t))) :=
  actualTranslatedNormalFamilyIdeal d t
    (fun a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) =>
      actualNormalHomogeneousPolynomial d t
        (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) (P.generator a)) p

/-- The entire untranslated ideal is the original actual normal-symbol ideal, in both directions. -/
theorem actualTranslatedNormalVertexIdeal_zero (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I) :
    actualTranslatedNormalVertexIdeal d t I P 0=actualAnalyticNormalVertexComponentIdeal d t I P := by
  unfold actualTranslatedNormalVertexIdeal actualTranslatedNormalFamilyIdeal
    actualAnalyticNormalVertexComponentIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact actualTranslatedNormalPolynomialEval_zero d t _

/-- EVERY genuine vertex family of the SAME original ideal supplies the genuine entire unshifted HS bound. -/
theorem hilbertSamuelValue_actualAnalyticNormalVertexComponentIdeal_le (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I) (ℓ : ℕ) :
    hilbertSamuelValue (actualAnalyticNormalVertexComponentIdeal d t I P) ℓ ≤ hilbertSamuelValue I ℓ := by
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

/-- Only the original ideal and its genuine vertex data are used; actual finite reindexing supplies ALL translated HS bounds. -/
theorem hilbertSamuelValue_actualTranslatedNormalVertexIdeal_le (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (p : Fin t → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualTranslatedNormalVertexIdeal d t I P p) ℓ ≤ hilbertSamuelValue I ℓ := by
  let V := actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let Q (a : V) := actualNormalHomogeneousPolynomial d t
    (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) (P.generator a)
  let q (i : Fin (Fintype.card V)) :=
    Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) (e i).val
  have hQ : ∀ i, (Q (e i)).IsHomogeneous (q i) :=
    fun i => actualNormalHomogeneousPolynomial_isHomogeneous d t _ _
  have hdict (b : Fin t → ℂ) : actualTranslatedNormalFamilyIdeal d t (Q ∘ e) b=
      actualTranslatedNormalVertexIdeal d t I P b := by
    unfold actualTranslatedNormalFamilyIdeal actualTranslatedNormalVertexIdeal
      actualTranslatedNormalFamilyIdeal
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro g ⟨i,rfl⟩
      exact Ideal.subset_span ⟨e i,rfl⟩
    · apply Ideal.span_le.mpr
      rintro g ⟨a,rfl⟩
      apply Ideal.subset_span
      refine ⟨e.symm a,?_⟩
      simp only [Function.comp_apply,Equiv.apply_symm_apply,Q]
  have h := hilbertSamuelValue_actual_translated_normal_le d t (Fintype.card V) (Q ∘ e) q hQ p ℓ
  rw [hdict p,hdict 0,actualTranslatedNormalVertexIdeal_zero] at h
  exact h.trans (hilbertSamuelValue_actualAnalyticNormalVertexComponentIdeal_le d t I P ℓ)

end
end Hironaka.HironakaActualTranslatedNormalVertexHS
