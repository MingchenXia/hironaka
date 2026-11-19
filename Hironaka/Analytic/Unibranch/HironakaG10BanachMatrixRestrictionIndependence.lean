import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
/-! The actual bounded source matrix does not depend on the chosen holomorphic window. -/
set_option autoImplicit false
open Set
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachMatrixRestrictionIndependence
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
noncomputable section
variable {Q X ι a r : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
  [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Fintype ι] [DecidableEq ι] [Fintype a] [Fintype r]

/-- Restriction to the same compact set gives the same whole bounded matrix
operator, independently of the open holomorphy window. -/
theorem banachMatrixCLM_eq_of_windows (b : Module.Basis ι ℂ Q)
    {K U V : Set X} [CompactSpace K] (hKU : K ⊆ U) (hKV : K ⊆ V)
    (F : a → r → X → Q) (hU : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hV : ∀ i j, DifferentiableOn ℂ (F i j) V) :
    banachMatrixCLM b hKU F hU = banachMatrixCLM b hKV F hV := by
  apply ContinuousLinearMap.ext
  intro v
  apply coefficientEvaluation_jointly_injective b
  intro z
  funext i
  rw [banachMatrix_evaluation,banachMatrix_evaluation]
end
end Hironaka.Analytic.Unibranch.HironakaG10BanachMatrixRestrictionIndependence
