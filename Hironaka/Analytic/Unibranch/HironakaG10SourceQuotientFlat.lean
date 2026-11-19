import Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10FlatNestedQuotientBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
import Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
import Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart

/-! Whole arbitrary-rank source matrix cokernels after actual substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientFlat
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange
  HironakaG10ArtinianFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
  Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10FlatNestedQuotientBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  OkaRelationSheaf
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- Flatness of the entire original centered joint-germ matrix cokernel
passes to the actual source-constructed tensor-germ matrix in every rank. -/
theorem quotient_centered_flat_gives_source_matrix_germ_flat
    (d t q : ℕ) {a b : ℕ} (I : Ideal (HolGerm (ComplexModel d)))
    {K : Set (ComplexModel t)} [CompactSpace K]
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (x : ComplexModel t) (hx : x ∈ interior K)
    (hflat : Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt 0 (centredMatrix d t F (0,x) i j)))))) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    letI : FiniteDimensional ℂ Q :=
      finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
    let data := normedComplexAlgebraData Q
    letI : NormedCommRing Q := data.1
    letI : NormedAlgebra ℂ Q := data.2.1
    let basis := Module.finBasis ℂ Q
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range (matrixGermMap basis x
        (sourceParameterMatrix (K := K) basis d q (parameterQuotientMap d q I) hF))) := by
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
  let : FiniteDimensional ℂ Q :=
    finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
  let data := normedComplexAlgebraData Q
  let : NormedCommRing Q := data.1
  let : NormedAlgebra ℂ Q := data.2.1
  let basis := Module.finBasis ℂ Q
  have hhol : ∀ i j, HolAt (F i j) (0,x) := by
    intro i j
    filter_upwards [hO.mem_nhds (hK x (interior_subset hx))] with z hz
    exact (hF i j z hz).differentiableAt (hO.mem_nhds hz)
  obtain ⟨hG,hmatrix⟩ := sourceParameterMatrix_germMap_eq_substitution d t q basis
    (parameterQuotientMap d q I) (parameterQuotientMap_kills d q I) hO hF hK x hx
  have hentry : (fun i j => (swapParameterFibre d t).symm
      (HolGerm.mk (sourceJointFibreFirst t d x (F i j)) (hG i j))) =
      (fun i j => germAt 0 (centredMatrix d t F (0,x) i j)) := by
    funext i j
    apply (swapParameterFibre d t).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (swapParameterFibre_native_centered t d x (F i j) (hhol i j) (hG i j)).symm
  let M : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))) :=
    fun i j => germAt 0 (centredMatrix d t F (0,x) i j)
  have hI : I ≤ truncatedParameterIdeal d q I := by
    change I ≤ I ⊔ _
    exact le_sup_left
  have hQ : Module.Flat Q (Q ⊗[HolGerm (ComplexModel d)]
      ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range M.mulVecLin)) :=
    flat_tensor_of_flat_quotient I (truncatedParameterIdeal d q I) hI hflat
  let _ := hQ
  have hresult := Module.Flat.of_linearEquiv (actualJointMatrixCokernelEquiv d t q I M).symm
  have hmap : (fun i j => actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
        (parameterQuotientMap_kills d q I) ((swapParameterFibre d t).symm
          (HolGerm.mk (sourceJointFibreFirst t d x (F i j)) (hG i j)))) =
      (fun i j => actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
        (parameterQuotientMap_kills d q I) (M i j)) := by
    funext i j
    exact congrArg _ (congrFun (congrFun hentry i) j)
  rw [hmap] at hmatrix
  change Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
    LinearMap.range (matrixGermMap basis x
      (sourceParameterMatrix (K := K) basis d q (parameterQuotientMap d q I) hF)))
  rw [hmatrix]
  exact hresult
end
end Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientFlat
