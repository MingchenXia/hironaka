import Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientFlat
import Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeSourceQuotientFlat
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange
  HironakaG10ArtinianFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
  Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientFlat
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
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

/-- Flatness of the original full product-stalk cokernel gives flatness of
the actual substituted source matrix germ over every finite parameter quotient. -/
theorem quotient_native_flat_gives_source_matrix_germ_flat
    (d t q : ℕ) {a b : ℕ} (I : Ideal (HolGerm (ComplexModel d)))
    {K : Set (ComplexModel t)} [CompactSpace K]
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (x : ComplexModel t) (hx : x ∈ interior K)
    (hflat : Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (0,x) (F i j)))))) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
    let data := normedComplexAlgebraData Q
    letI : NormedCommRing Q := data.1
    letI : NormedAlgebra ℂ Q := data.2.1
    let basis := Module.finBasis ℂ Q
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range (matrixGermMap basis x
        (sourceParameterMatrix (K := K) basis d q (parameterQuotientMap d q I) hF))) := by
  have hhol : ∀ i j, HolAt (F i j) (0,x) := by
    intro i j
    filter_upwards [hO.mem_nhds (hK x (interior_subset hx))] with z hz
    exact (hF i j z hz).differentiableAt (hO.mem_nhds hz)
  let R := HolGerm (ComplexModel d)
  let B := R ⧸ I
  let C := ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range
    (Matrix.mulVecLin (fun i j => germAt 0 (centredMatrix d t F (0,x) i j))))
  let D := ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
    (Matrix.mulVecLin (fun i j => germAt (0,x) (F i j))))
  have hc : Module.Flat B (B ⊗[R] C) := by
    let _ := hflat
    exact Module.Flat.of_linearEquiv ((centeredNativeMatrixCokernelEquiv d t F x hhol).baseChange R B C D)
  exact quotient_centered_flat_gives_source_matrix_germ_flat d t q I hO hF hK x hx hc
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeSourceQuotientFlat
