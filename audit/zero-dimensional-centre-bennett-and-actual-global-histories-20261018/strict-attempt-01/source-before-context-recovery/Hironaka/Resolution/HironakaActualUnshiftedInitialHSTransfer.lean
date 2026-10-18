/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.TranslatedInitialHSOriginalExact
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! The genuine translated initial comparison in the original unshifted analytic coordinate ring. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualUnshiftedInitialHSTransfer
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaActualOriginalFormalTaylor HironakaActualOriginalFormalHSTransfer
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualFormalInitialDiagram HironakaActualFiniteInitialGeneration HironakaActualTranslatedInitialHS
variable {n : ℕ}

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

/-- The original whole Taylor quotient equivalence retains every actual unshifted analytic HS value. -/
theorem hilbertSamuelValue_eq_actual_unshifted_formal_extension (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ =
      genuineFormalHilbertSamuelValue n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) ℓ := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m))) (ℓ : ℕ),
      hilbertSamuelValue J ℓ=genuineFormalHilbertSamuelValue n (Ideal.map f.toRingHom J) ℓ
  exact unshiftedTaylor_property n P (hilbertSamuelValue_eq_genuine_formal_extension n) I ℓ

/-- Genuine finite polynomial translation at the same actual original coordinate germs. -/
def actualUnshiftedTranslatedPolynomialEval (n : ℕ) (p : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] HolGerm (ComplexModel n) :=
  MvPolynomial.aeval (fun i => coordinateGerm i+algebraMap ℂ _ (p i))

/-- The entire original analytic ideal uses the unchanged actual finite initial vertex polynomials. -/
def actualUnshiftedTranslatedInitialIdeal (K : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ) :
    Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex K =>
    actualUnshiftedTranslatedPolynomialEval n p (actualInitialVertexPolynomial K a))

/-- Genuine Taylor coordinates identify both whole translated ideals, without any supplied dictionary. -/
theorem actualUnshiftedTranslatedInitialIdeal_formal_extension
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualUnshiftedTranslatedInitialIdeal K p)=
      actualTranslatedInitialFormalIdeal K p := by
  have hm : (actualUnshiftedTaylorAlgHom n).comp (actualUnshiftedTranslatedPolynomialEval n p)=
      MvPolynomial.aeval (fun i => MvPowerSeries.X i+algebraMap ℂ _ (p i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change actualUnshiftedTaylorAlgHom n (actualUnshiftedTranslatedPolynomialEval n p (MvPolynomial.X i))=_
    simp only [actualUnshiftedTranslatedPolynomialEval,MvPolynomial.aeval_X,map_add,
      actualUnshiftedTaylor_coordinate,AlgHom.commutes]
  rw [actualUnshiftedTranslatedInitialIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact DFunLike.congr_fun hm (actualInitialVertexPolynomial K a)

/-- Every true translated original finite initial ideal has all values bounded by the original formal ideal. -/
theorem hilbertSamuelValue_actual_unshifted_translated_initial_le
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal K p) ℓ ≤
      genuineFormalHilbertSamuelValue n K ℓ := by
  rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    actualUnshiftedTranslatedInitialIdeal_formal_extension]
  exact genuineFormalHilbertSamuelValue_translated_initial_le K p ℓ

/-- Only the actual original ideal supplies its entire translated-initial HS comparison at every order. -/
theorem hilbertSamuelValue_actual_original_translated_initial_le (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (p : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) p) ℓ ≤ hilbertSamuelValue I ℓ := by
  rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension n I]
  exact hilbertSamuelValue_actual_unshifted_translated_initial_le _ p ℓ

end
end Hironaka.HironakaActualUnshiftedInitialHSTransfer
