import Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixOperatorJet
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator

/-! # Actual source operator jet in the Artinian coefficient model -/
set_option autoImplicit false
open Set
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixOperatorJet

/-- The actual source matrix-operator jet, transported to the whole finite
coefficient model, is exactly the actual Artinian matrix operator. -/
theorem sourceCoefficientOperator_eq_artinian
    {Q X r a ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K₀ K₁ : Set X} [CompactSpace K₀] [CompactSpace K₁]
    [Fintype r] [Fintype a] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : a → r → ComplexModel d × X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O) (hK₁ : K₁ ⊆ interior K₀) :
    ∃ hFQ : ∀ i j, DifferentiableOn ℂ
      (sourceParameterMatrix (K := K₀) b d q φ hF i j) (interior K₀),
      coefficientTensorOperator (E := r → holSubalgebra K₁) (F := a → holSubalgebra K₁) b
        (banachJet (E := (r → holSubalgebra K₁) →L[ℂ] (a → holSubalgebra K₁)) d q φ
          (fun s => matrixOperator (fun i j => restrictParam K₁ (hF i j) s))) =
      (banachMatrixCLM b hK₁ (sourceParameterMatrix (K := K₀) b d q φ hF) hFQ).toLinearMap := by
  obtain ⟨hFQ,h⟩ := sourceMatrixOperatorJet_eq_artinian_whole b d q φ hφ hO hF hK₀ hK₁
  refine ⟨hFQ,?_⟩
  apply LinearMap.ext
  intro v
  exact h v

end Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator
