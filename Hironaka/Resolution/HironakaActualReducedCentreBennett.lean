/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoefficientCentreBennett

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualReducedCentreBennett
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualAnalyticVertexCoefficientData HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualCoefficientReducedStrictGenerators
  HironakaActualAnalyticCentreVertexFamily HironakaActualFiniteCoefficientIdeals
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualAnalyticFormalNormalPowers
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualNormalAxisDehomogenization HironakaActualTranslatedNormalVertexHS
  HironakaActualNormalBlowupExceptionalLocus HironakaActualAnalyticStrictGenerators
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett

/-- Literal reduced formal centre powers internally choose SAME analytic vertex data retaining actual normal powers. -/
theorem exists_actual_reduced_centre_vertex_data (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) :
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I,
      ∀ a,P.generator a ∈ normalIdeal d t ^
        Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨G,hG,hspan⟩ := exists_actual_analytic_centre_vertex_family (d+t) I
    (actualTangentCentreVariables d t) hV
  let J := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I
  let q := ∑ a : actualInitialVertices MonomialOrder.degLex J,
    actualCoefficientCentreVertexWeight d 0 t a.val
  have hle (a : actualInitialVertices MonomialOrder.degLex J) :
      actualCoefficientCentreVertexWeight d 0 t a.val ≤ q :=
    Finset.single_le_sum
      (f := fun a : actualInitialVertices MonomialOrder.degLex J =>
        actualCoefficientCentreVertexWeight d 0 t a.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  obtain ⟨U,hU,h0,c,hc,hd,hT,_⟩ := exists_actual_finite_local_coefficient_ideals (d+0) t q G
  have hd' (a : actualInitialVertices MonomialOrder.degLex J) (γ : Fin t →₀ ℕ)
      (hγ : actualNormalDegree γ<
        actualCoefficientCentreVertexWeight d 0 t a.val) :=
    hd a γ (lt_of_lt_of_le hγ (hle a))
  refine ⟨{
    generator := G
    member := fun a => (hG a).1
    nonzero := fun a => (hG a).2.2.choose
    initial := fun a => (hG a).2.2.choose_spec.1
    monic := fun a => (hG a).2.2.choose_spec.2
    generates := hspan
    domain := U
    isOpen_domain := hU
    zero_mem_domain := h0
    coefficient := c
    holomorphic := hc
    regular := fun a γ hγ => (hd' a γ hγ).1
    coherent := fun a γ hγ => (hd' a γ hγ).2.1
    coefficient_member := fun a γ hγ => (hd' a γ hγ).2.2
    coefficient_eq := hT },?_⟩
  intro a
  apply (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (G a)).mpr
  exact actualTaylor_mem_coordinateCentre_pow _ _ _ (hG a).2.1

/-- Only the SAME canonical reduced formal centre property is supplied; all compatible analytic data are internal. -/
theorem hilbertSamuelValue_actual_reduced_centre_normalized_le (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) ℓ ≤
      hilbertSamuelValue I ℓ := by
  obtain ⟨P,hP⟩ := exists_actual_reduced_centre_vertex_data d t I hV
  have h := hilbertSamuelValue_actual_normal_normalized_le_translated d t I P.generator
    (fun a => Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    P.member hP j b ℓ
  exact h.trans (hilbertSamuelValue_actualTranslatedNormalVertexIdeal_le d t I P _ ℓ)

/-- The original intrinsic geometric strict-transform inequality, with only literal original reduced formal centre powers. -/
theorem hilbertSamuelAt_actual_reduced_centre_strict_le (d t : ℕ)
    (W : Set (ComplexModel (d+t)))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))) a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) 0 ℓ := by
  by_cases ht : t=1
  · subst t
    exact (hilbertSamuelAt_actual_normal_blowup_one d j b W ℓ).le
  · have hj := j.isLt
    apply (hilbertSamuelAt_actual_normal_strict_le_normalized d t (by omega) j b W ℓ).trans
    rw [hilbertSamuelAt_model_zero]
    exact hilbertSamuelValue_actual_reduced_centre_normalized_le d t _ hV j b ℓ

end
end Hironaka.HironakaActualReducedCentreBennett
