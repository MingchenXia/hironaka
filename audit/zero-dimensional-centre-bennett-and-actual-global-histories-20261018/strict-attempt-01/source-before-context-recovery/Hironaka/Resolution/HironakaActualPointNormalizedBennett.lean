/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointUnitCoordinateChange
import Hironaka.Resolution.HironakaActualPointInitialIdealInclusion
import Hironaka.Resolution.HironakaActualUnshiftedInitialHSTransfer
import Hironaka.Resolution.HironakaActualPointCentreStrictGenerators

/-! All-order point-normalized HS comparison in the original analytic ring, and its actual formal extension. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointNormalizedBennett
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualFiniteInitialGeneration HironakaActualTranslatedInitialHS
  HironakaActualOriginalFormalHSTransfer HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticStrictGenerators HironakaActualPointCentreStrictGenerators
  HironakaActualFormalStrictGenerators HironakaActualPointDehomogenizedInitial
  HironakaActualPointUnitCoordinateChange HironakaActualPointInitialIdealInclusion
  HironakaActualUnshiftedInitialHSTransfer
variable {n : ℕ}

/-- True unit factors identify both entire actual finite initial ideals under the genuine coordinate equivalence. -/
theorem map_actualDehomogenizedInitialIdeal_unit_coordinates
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (actualPointUnitGermEquiv e b).toRingEquiv.toRingHom
        (actualDehomogenizedInitialIdeal K e b)=
      actualUnshiftedTranslatedInitialIdeal K (actualPointUnitBasePoint e b) := by
  have hdict (a : actualInitialVertices MonomialOrder.degLex K) :
      actualPointUnitGermEquiv e b
          (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
            (actualPointDehomogenization e b (actualInitialVertexPolynomial K a)))=
        (actualPointUnitReciprocal e)^(normalExponentDegree a.val)*
          actualUnshiftedTranslatedPolynomialEval n (actualPointUnitBasePoint e b) (actualInitialVertexPolynomial K a) :=
    actualPointUnitGermEquiv_dehomogenization e b _ _ (actualInitialVertexPolynomial_isHomogeneous K a)
  apply le_antisymm
  · rw [actualDehomogenizedInitialIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨f,⟨a,rfl⟩,rfl⟩
    change actualPointUnitGermEquiv e b
      (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
        (actualPointDehomogenization e b (actualInitialVertexPolynomial K a))) ∈ _
    rw [hdict a]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := a))
  · apply Ideal.span_le.mpr
    rintro g ⟨a,rfl⟩
    have hmem := Ideal.mem_map_of_mem (actualPointUnitGermEquiv e b).toRingEquiv.toRingHom
      (show MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
        (actualPointDehomogenization e b (actualInitialVertexPolynomial K a)) ∈
          actualDehomogenizedInitialIdeal K e b from Ideal.mem_span_range_self (x := a))
    have hprod : (1+coordinateGerm e)^(normalExponentDegree a.val)*
        actualPointUnitGermEquiv e b
          (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
            (actualPointDehomogenization e b (actualInitialVertexPolynomial K a)))=
          actualUnshiftedTranslatedPolynomialEval n (actualPointUnitBasePoint e b) (actualInitialVertexPolynomial K a) := by
      rw [hdict a,← mul_assoc,← mul_pow,actualPointUnit_mul_reciprocal,one_pow,one_mul]
    change actualUnshiftedTranslatedPolynomialEval n (actualPointUnitBasePoint e b) (actualInitialVertexPolynomial K a) ∈ _
    rw [← hprod]
    exact Ideal.mul_mem_left _ _ hmem

/-- The SAME actual dehomogenized and translated finite initial ideals have identical values at every order. -/
theorem hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualDehomogenizedInitialIdeal K e b) ℓ=
      hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal K (actualPointUnitBasePoint e b)) ℓ := by
  rw [← map_actualDehomogenizedInitialIdeal_unit_coordinates]
  exact (hilbertSamuelValue_actualPointUnitGermEquiv e b _ ℓ).symm

/-- ONLY the original analytic ideal and point chart give ALL intrinsic normalized-member HS inequalities. -/
theorem hilbertSamuelValue_actual_point_normalized_le_original (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I Set.univ e b) ℓ ≤ hilbertSamuelValue I ℓ := by
  calc
    _ ≤ hilbertSamuelValue (actualDehomogenizedInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) e b) ℓ :=
      hilbertSamuelValue_actual_point_normalized_le_dehomogenized_initial n I e b ℓ
    _ = hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) (actualPointUnitBasePoint e b)) ℓ :=
      hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated _ e b ℓ
    _ ≤ hilbertSamuelValue I ℓ :=
      hilbertSamuelValue_actual_original_translated_initial_le n I (actualPointUnitBasePoint e b) ℓ

/-- The whole actual point formal strict ideal of EVERY analytic extension retains the same all-order bound. -/
theorem genuineFormalHilbertSamuelValue_actual_point_strict_le_original (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n
        (actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
          Set.univ e (mem_univ e) b) ℓ ≤
      genuineFormalHilbertSamuelValue n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) ℓ := by
  obtain ⟨H,_hgen,hformal⟩ := exists_actual_point_normalized_member_generators n I e b
  calc
    _ = hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I Set.univ e b) ℓ := by
      rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,hformal]
    _ ≤ hilbertSamuelValue I ℓ := hilbertSamuelValue_actual_point_normalized_le_original n I e b ℓ
    _ = _ := hilbertSamuelValue_eq_actual_unshifted_formal_extension n I ℓ

end
end Hironaka.HironakaActualPointNormalizedBennett
