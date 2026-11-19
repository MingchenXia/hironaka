import Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurMatrixFlat
import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurJetFlat
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10LocFrischLocus
  HironakaG10LocDirectPersistence HironakaG10FlatPrivilegedEuclidean HironakaHolomorphicPointJets
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible
  Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurMatrixFlat
noncomputable section
local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    Algebra ℂ (HolGerm X) := (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

theorem varying_schur_jet_zero_forces_matrix_flat
    {Q ι : Type} {n : ℕ} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι]
    {K U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace K]
    (hK : K ∈ closedPolydiscs n) (hU : IsOpen U) (hKU : K ⊆ U) {a r c : ℕ}
    (F₀ : Fin a → Fin r → holSubalgebra K) (G₀ : Fin r → Fin c → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin r → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin r → holSubalgebra K))
    (hR : ∀ x, matrixOperator G₀ (R₀ (matrixOperator G₀ x)) = matrixOperator G₀ x)
    (hS : ∀ x, matrixOperator F₀ (S₀ (matrixOperator F₀ x)) = matrixOperator F₀ x)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤ RingHom.ker φ.toRingHom)
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n : ℕ, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (F : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (Fr : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → ℂ)
    (hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U)
    (hres : ∀ x ∈ U, ∀ i j, ε (F i j x) = Fr i j x)
    (f : ComplexModel d → ((Fin r → holSubalgebra K) →L[ℂ] (Fin a → holSubalgebra K)))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hf0 : f 0 = matrixOperator (restrictMatrix K hKU Fr hFr))
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀ (f 0)).IsInvertible)
    (hcoeff : coefficientTensorOperator b (banachJet d q φ f) = (banachMatrixCLM b hKU F hF).toLinearMap)
    (hjet : banachJet d q φ (fun s => schurOp ((matrixOperator G₀).comp R₀)
      ((matrixOperator F₀).comp S₀) S₀ (f s)) = 0)
    (hDirect : DirectExact
      (fun j l => kerSec ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (matrixOperator (restrictMatrix K hKU Fr hFr)) (fun j' => G₀ j' l) j)
      (restrictMatrix K hKU Fr hFr)) :
    ∀ z ∈ interior K, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
      LinearMap.range (matrixGermMap b z F)) := by
  let P := (matrixOperator G₀).comp R₀
  let T := (matrixOperator F₀).comp S₀
  let Fcoeff := banachMatrixCLM b hKU F hF
  obtain ⟨hCQ,_⟩ := coefficient_actual_inverse_jet_of_invertible b d q φ hφ P T S₀ f hf hC Fcoeff hcoeff
  have hj := coefficient_actual_schur_jet_of_invertible b d q φ hφ P T S₀ f hf hC Fcoeff hcoeff
  rw [hjet] at hj
  have hSchur : schurOp (coefficientCLM P) (coefficientCLM T) (coefficientCLM S₀) Fcoeff = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply funext
    intro i
    have hv := congrFun (LinearMap.congr_fun hj v) i
    simpa [coefficientTensorOperator] using hv.symm
  have hP : coefficientCLM (ι := ι) P = (coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀) := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    rfl
  have hT : coefficientCLM (ι := ι) T = (coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀) := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    rfl
  apply matrixGermMap_flat_of_varying_schur_zero hK hU hKU F₀ G₀ hex R₀ S₀ hR hS b ε hnil F hF Fr hFr hres
  · simpa only [hf0] using hC
  · simpa only [hP,hT,Fcoeff] using hCQ
  · simpa only [hP,hT,Fcoeff] using hSchur
  · exact hDirect
end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurJetFlat
