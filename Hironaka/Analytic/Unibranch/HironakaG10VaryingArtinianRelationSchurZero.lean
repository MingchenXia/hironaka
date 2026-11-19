import Hironaka.Analytic.Unibranch.HironakaG10ActualVaryingRelationSchurZero
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpAInvertible
import Hironaka.Analytic.Unibranch.HironakaG10VaryingReferenceInvertibility
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingArtinianRelationSchurZero
open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.HironakaG10FlatResolutionStart
  Hironaka.HironakaG10LocDirectPersistence
  Hironaka.HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ActualVaryingRelationSchurZero
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpAInvertible
  Hironaka.Analytic.Unibranch.HironakaG10VaryingReferenceInvertibility
noncomputable section

theorem artinian_relation_with_invertible_current_reference_forces_old_schur_zero
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    {a r c : Type*} [Fintype a] [Fintype r] [Fintype c]
    {K U : Set X} [CompactSpace K] (hKU : K ⊆ U)
    (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (F₀ : a → r → holSubalgebra K) (G₀ : r → c → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (r → holSubalgebra K) →L[ℂ] (c → holSubalgebra K))
    (S₀ : (a → holSubalgebra K) →L[ℂ] (r → holSubalgebra K))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : r → c → holSubalgebra K)
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr)).IsInvertible)
    (F : a → r → X → Q) (G : r → c → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hG : ∀ j l, DifferentiableOn ℂ (G j l) U)
    (hFG : ∀ (z : K) i l, ∑ j, F i j z * G j l z = 0)
    (hred : ∀ (z : K) j l, ε (G j l z) = (Gr j l : C(K,ℂ)) z)
    (hC : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU F hF)).IsInvertible) :
    schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU F hF) = 0 := by
  let := parameterCoefficientModule (E := c → holSubalgebra K) basis
  let := parameterCoefficientModule (E := r → holSubalgebra K) basis
  obtain ⟨hB,BInvA,hInv⟩ := coefficient_opA_invertible_parameter_inverse basis
    (matrixOperator G₀) (matrixOperator Gr) R₀ hRef
  have hmod := banachMatrix_reduction_error basis ε hKU G hG Gr hred
  have hA := opA_invertible_of_invertible_reference basis (matrixOperator G₀) R₀
    (matrixOperator Gr) (RingHom.ker ε.toRingHom) hnil
    (banachMatrixCLM basis hKU G hG) (banachMatrixLinear basis hKU G hG)
    (fun _ => rfl) hB BInvA hInv hmod
  exact actual_relation_forces_old_schur_zero hKU basis F₀ G₀ hex R₀ S₀ hR hS F G hF hG hFG hA hC
end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingArtinianRelationSchurZero
