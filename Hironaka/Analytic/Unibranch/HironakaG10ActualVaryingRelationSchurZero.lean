import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
import Hironaka.Analytic.Unibranch.HironakaG10NilpotentKernelSchur
set_option autoImplicit false
open Set
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualVaryingRelationSchurZero
open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.HironakaG10FlatResolutionStart
  Hironaka.HironakaG10LocDirectPersistence
  Hironaka.HironakaG10LocProductExact
  Hironaka.HironakaG10LocFrischLocus
  Hironaka.HironakaG10LocFrischUniversal
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
noncomputable section

theorem actual_relation_forces_old_schur_zero
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    {a r c : Type*} [Fintype a] [Fintype r] [Fintype c]
    {K U : Set X} [CompactSpace K] (hKU : K ⊆ U)
    (basis : Module.Basis ι ℂ Q)
    (F₀ : a → r → holSubalgebra K) (G₀ : r → c → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (r → holSubalgebra K) →L[ℂ] (c → holSubalgebra K))
    (S₀ : (a → holSubalgebra K) →L[ℂ] (r → holSubalgebra K))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (F : a → r → X → Q) (G : r → c → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hG : ∀ j l, DifferentiableOn ℂ (G j l) U)
    (hFG : ∀ (z : K) i l, ∑ j, F i j z * G j l z = 0)
    (hA : (opA ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      (coefficientCLM R₀) (banachMatrixCLM basis hKU G hG)).IsInvertible)
    (hC : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU F hF)).IsInvertible) :
    schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU F hF) = 0 := by
  have hcomp : ∀ e, matrixOperator F₀ (matrixOperator G₀ e) = 0 :=
    matrixOperator_comp_apply _ _ hex.comp
  obtain ⟨hR',hS',_,hExact⟩ := reference_direct_exact_on_coefficients (ι := ι)
    (matrixOperator G₀) (matrixOperator F₀) R₀ S₀ hR hS hcomp hex.exact
  have hzero := banachMatrix_comp_eq_zero basis hKU F G hF hG hFG
  apply (schurOp_eq_zero_iff hR' hS' hExact hC).mpr
  intro x
  refine ⟨banachMatrixCLM basis hKU G hG (rinv
    ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
    (coefficientCLM R₀) (banachMatrixCLM basis hKU G hG) x), ?_, ?_⟩
  · exact congrFun (congrArg DFunLike.coe hzero) _
  · exact P_g_rinv hR' hA x
end
end Hironaka.Analytic.Unibranch.HironakaG10ActualVaryingRelationSchurZero
