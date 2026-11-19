import Hironaka.Analytic.Unibranch.HironakaG10SchurParameterRelation
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorRelation
import Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
import Hironaka.Resolution.HironakaG10FlatResolutionStart

/-! The actual finite-coefficient Schur obstruction gives actual
holomorphic relation columns over a nilpotent parameter algebra. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurHolomorphicRelation
open Hironaka HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorRelation
  Hironaka.Analytic.Unibranch.HironakaG10SchurParameterRelation
noncomputable section

/-- No flatness assumption: the literal coefficient Schur vanishing and
nilpotent residue produce holomorphic relation columns with exact residue. -/
theorem exists_holomorphic_relation_of_artinian_schur_zero
    {Q X ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    {K U : Set X} [CompactSpace K] (hKU : K ⊆ U) {a r c : ℕ}
    (F₀ : Fin a → Fin r → holSubalgebra K) (G₀ : Fin r → Fin c → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin r → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin r → holSubalgebra K))
    (hR : ∀ x, matrixOperator G₀ (R₀ (matrixOperator G₀ x)) = matrixOperator G₀ x)
    (hS : ∀ x, matrixOperator F₀ (S₀ (matrixOperator F₀ x)) = matrixOperator F₀ x)
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n : ℕ, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (F : Fin a → Fin r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hres : ∀ (z : K) i j, ε (F i j z) = ((F₀ i j : holSubalgebra K) : C(K,ℂ)) z)
    (hSchur : schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM b hKU F hF) = 0) :
    ∃ G : Fin r → Fin c → X → Q,
      (∀ j l, DifferentiableOn ℂ (G j l) (interior K)) ∧
      (∀ x ∈ interior K, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
      (∀ x (hx : x ∈ interior K), ∀ j l,
        ε (G j l x) = ((G₀ j l : holSubalgebra K) : C(K,ℂ)) ⟨x, interior_subset hx⟩) := by
  let g₀ := matrixOperator G₀
  let f₀ := matrixOperator F₀
  have hcomp : ∀ x, f₀ (g₀ x) = 0 := matrixOperator_comp_apply _ _ hex.comp
  obtain ⟨hR',hS',hcomp',hex'⟩ := reference_direct_exact_on_coefficients (ι := ι)
    g₀ f₀ R₀ S₀ hR hS hcomp hex.exact
  let := parameterCoefficientModule (E := Fin c → holSubalgebra K) b
  let := parameterCoefficientModule (E := Fin r → holSubalgebra K) b
  let := parameterCoefficientModule (E := Fin a → holSubalgebra K) b
  let f := banachMatrixCLM b hKU F hF
  let FA := banachMatrixLinear b hKU F hF
  let F₀A := coefficientMap b f₀.toLinearMap
  let G₀A := coefficientMap b g₀.toLinearMap
  let PA := coefficientMap b (g₀.comp R₀).toLinearMap
  let QA := coefficientMap b (f₀.comp S₀).toLinearMap
  let SA := coefficientMap b S₀.toLinearMap
  have hFA (x) : FA x = f x := rfl
  have hF₀A (x) : F₀A x = coefficientCLM f₀ x := coefficientCLM_eq_parameterMap b f₀ x
  have hG₀A (x) : G₀A x = coefficientCLM g₀ x := coefficientCLM_eq_parameterMap b g₀ x
  have hPA (x) : PA x = coefficientCLM g₀ (coefficientCLM R₀ x) := by
    funext i
    simp [PA, coefficientMap_apply, coefficientCLM_apply]
  have hQA (x) : QA x = coefficientCLM f₀ (coefficientCLM S₀ x) := by
    funext i
    simp [QA, coefficientMap_apply, coefficientCLM_apply]
  have hSA (x) : SA x = coefficientCLM S₀ x := coefficientCLM_eq_parameterMap b S₀ x
  have hmod : ∀ x, FA x - F₀A x ∈ RingHom.ker ε.toRingHom •
      (⊤ : Submodule Q (ι → Fin a → holSubalgebra K)) :=
    banachMatrix_reduction_error b ε hKU F hF F₀ hres
  have hC := opC_invertible_on_nilpotent_coefficients b g₀ f₀ R₀ S₀ hcomp
    (RingHom.ker ε.toRingHom) hnil f FA hFA hmod
  obtain ⟨T,hrel,hmodT⟩ := exists_parameter_relation_of_schur_zero
    (A := Q) (E₂ := ι → Fin c → holSubalgebra K)
    (E₁ := ι → Fin r → holSubalgebra K) (E₀ := ι → Fin a → holSubalgebra K)
    (RingHom.ker ε.toRingHom) (coefficientCLM g₀) (coefficientCLM f₀)
    (coefficientCLM R₀) (coefficientCLM S₀) hR' hS' hex' hcomp'
    f FA F₀A G₀A PA QA SA hFA hF₀A hG₀A hPA hQA hSA hmod hC hSchur
  apply exists_holomorphic_relation_of_coefficient_lift b ε hKU F hF G₀ T
  · exact hrel
  · exact hmodT
end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurHolomorphicRelation
