import Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
import Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
import Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift

/-! # Whole original source matrix as an actual substituted stalk matrix -/
set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
open Hironaka Hironaka
  OkaRelationSheaf HironakaG10ArtinianParameterPullback
  Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift

/-- The literal source matrix's whole germ presentation is the matrix of
actual substitutions of its original, recentered joint entry germs. -/
theorem sourceParameterMatrix_germMap_eq_substitution
    {Q : Type*} {ι a k : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a] [Fintype k] [DecidableEq k]
    (d t q : ℕ) {K : Set (ComplexModel t)} [CompactSpace K]
    (b : Module.Basis ι ℂ Q) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : a → k → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (x : ComplexModel t) (hx : x ∈ interior K) :
    ∃ hG : ∀ i j, HolAt (sourceJointFibreFirst t d x (F i j)) 0,
      matrixGermMap b x (sourceParameterMatrix (K := K) b d q φ hF) =
        (Matrix.mulVecLin (fun i j => actualArtinianParameterPullback d t q φ hφ
          ((swapParameterFibre d t).symm (HolGerm.mk (sourceJointFibreFirst t d x (F i j))
            (hG i j))))).restrictScalars Q := by
  classical
  choose hG hGerm using fun i j =>
    sourceParameterExtension_tensorGerm d t q b φ hφ hO (hF i j) hK x hx
  refine ⟨hG,?_⟩
  apply LinearMap.ext
  intro v
  funext i
  rw [matrixGermMap_apply]
  change (∑ j, tensorGermAt b x (sourceParameterMatrix (K := K) b d q φ hF i j) * v j) =
    (∑ j, actualArtinianParameterPullback d t q φ hφ
      ((swapParameterFibre d t).symm (HolGerm.mk (sourceJointFibreFirst t d x (F i j))
        (hG i j))) * v j)
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceParameterMatrix, hGerm i j]

end Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
