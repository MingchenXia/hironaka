import Hironaka.Analytic.Unibranch.HironakaG10KernelSectionResidue
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientColumnRelation
import Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorRelation
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurRelation
open Hironaka HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorRelation
  Hironaka.Analytic.Unibranch.HironakaG10KernelSectionResidue
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientColumnRelation
noncomputable section

theorem exists_varying_schur_holomorphic_relation
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
    (F : Fin a → Fin r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (Fr : Fin a → Fin r → holSubalgebra K)
    (hres : ∀ (z : K) i j, ε (F i j z) = ((Fr i j : holSubalgebra K) : C(K,ℂ)) z)
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (matrixOperator Fr)).IsInvertible)
    (hCQ : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM b hKU F hF)).IsInvertible)
    (hSchur : schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM b hKU F hF) = 0) :
    let Gr : Fin r → Fin c → holSubalgebra K := fun j l =>
      kerSec ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (matrixOperator Fr) (fun j' => G₀ j' l) j
    ∃ G : Fin r → Fin c → X → Q,
      (∀ j l, DifferentiableOn ℂ (G j l) (interior K)) ∧
      (∀ x ∈ interior K, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
      (∀ x (hx : x ∈ interior K), ∀ j l,
        ε (G j l x) = ((Gr j l : holSubalgebra K) : C(K,ℂ)) ⟨x, interior_subset hx⟩) := by
  let g₀ := matrixOperator G₀
  let f₀ := matrixOperator F₀
  let fr := matrixOperator Fr
  let fq := banachMatrixCLM b hKU F hF
  let P := g₀.comp R₀
  let T := f₀.comp S₀
  let PQ : (ι → Fin r → holSubalgebra K) →L[ℂ] (ι → Fin r → holSubalgebra K) :=
    (coefficientCLM g₀).comp (coefficientCLM R₀)
  let TQ : (ι → Fin a → holSubalgebra K) →L[ℂ] (ι → Fin a → holSubalgebra K) :=
    (coefficientCLM f₀).comp (coefficientCLM S₀)
  let Gr : Fin r → Fin c → holSubalgebra K := fun j l => kerSec P T S₀ fr (fun j' => G₀ j' l) j
  have hcomp : ∀ x, f₀ (g₀ x) = 0 := matrixOperator_comp_apply _ _ hex.comp
  obtain ⟨hR',hS',_hcomp',hex'⟩ := reference_direct_exact_on_coefficients (ι := ι)
    g₀ f₀ R₀ S₀ hR hS hcomp hex.exact
  let v : Fin c → ι → Fin r → holSubalgebra K := fun l =>
    kerSec PQ TQ (coefficientCLM S₀) fq
      (coefficientCLM g₀ (unitCoefficientColumn b K l))
  have hker (l : Fin c) : fq (v l) = 0 :=
    f_kerSec hR' hS' hex' hCQ hSchur _
  have hred (w : ι → Fin r → holSubalgebra K) :
      coefficientResidue b ε (fq w) = fr (coefficientResidue b ε w) :=
    coefficientResidue_banachMatrix b ε hKU F hF Fr hres w
  have hcoeffP : coefficientCLM P = PQ := by ext x i; rfl
  have hcoeffT : coefficientCLM T = TQ := by ext x i; rfl
  have hrv (l : Fin c) : coefficientResidue b ε (v l) = fun j => Gr j l := by
    dsimp only [v,Gr]
    rw [← hcoeffP, ← hcoeffT]
    rw [coefficientResidue_kerSec b ε P T S₀ fq fr hred hC]
    · rw [coefficientResidue_coefficientCLM, unitCoefficientColumn_residue]
      have hcol : g₀ (Pi.single l 1) = fun j => G₀ j l := by
        funext j
        simp [g₀, matrixOperator_apply, Pi.single_apply, apply_ite]
      rw [hcol]
    · simpa only [hcoeffP,hcoeffT] using hCQ
  exact exists_holomorphic_relation_of_coefficient_columns b ε hKU F hF Gr v hker hrv
end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurRelation
