import Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10FlatNestedQuotientBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
import Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
import Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
import Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank

/-! Whole arbitrary-rank source matrix cokernels after actual substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientReverse
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange
  HironakaG10ArtinianFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
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
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- Flatness of the literal substituted source matrix germ passes back to
the same native product-stalk cokernel after the finite parameter base change. -/
theorem source_matrix_germ_flat_gives_quotient_native_flat
    (d t q : ℕ) {a b : ℕ} (I : Ideal (HolGerm (ComplexModel d)))
    {K : Set (ComplexModel t)} [CompactSpace K]
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (x : ComplexModel t) (hx : x ∈ interior K)
    (hflat :
      let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
      letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
      let data := normedComplexAlgebraData Q
      letI : NormedCommRing Q := data.1
      letI : NormedAlgebra ℂ Q := data.2.1
      let basis := Module.finBasis ℂ Q
      Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
        LinearMap.range (matrixGermMap basis x
          (sourceParameterMatrix (K := K) basis d q (parameterQuotientMap d q I) hF)))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I)
      ((HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (0,x) (F i j))))) := by
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
      (sourceParameterMatrix (K := K) basis d q (parameterQuotientMap d q I) hF))) at hflat
  have hf' : Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range ((Matrix.mulVecLin (fun i j => actualArtinianParameterPullback d t q
        (parameterQuotientMap d q I) (parameterQuotientMap_kills d q I) (M i j))).restrictScalars Q)) := by
    rw [hmatrix] at hflat
    exact hflat
  letI := hf'
  have hc : Module.Flat Q (Q ⊗[HolGerm (ComplexModel d)]
      ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range M.mulVecLin)) :=
    Module.Flat.of_linearEquiv (actualJointMatrixCokernelEquiv d t q I M)
  letI := hc
  exact Module.Flat.of_linearEquiv
    ((centeredNativeMatrixCokernelEquiv d t F x hhol).baseChange (HolGerm (ComplexModel d)) Q _ _).symm
end
end Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientReverse
