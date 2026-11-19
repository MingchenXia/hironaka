import Hironaka.Analytic.Unibranch.HironakaG10SourceHigherRankFlat
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange
  HironakaG10ArtinianFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
  Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10SourceHigherRankFlat
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

/-- The actual product-stalk matrix cokernel and the centered joint-germ
matrix cokernel retain the same original parameter action. -/
def centeredNativeMatrixCokernelEquiv
    (d t : ℕ) {a b : ℕ} (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (x : ComplexModel t) (hF : ∀ i j, HolAt (F i j) (0,x)) :
    ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range
      (Matrix.mulVecLin (fun i j => germAt 0 (centredMatrix d t F (0,x) i j)))) ≃ₗ[HolGerm (ComplexModel d)]
    ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
      (Matrix.mulVecLin (fun i j => germAt (0,x) (F i j)))) := by
  let R := HolGerm (ComplexModel d)
  let A := HolGerm (ComplexModel (d+t))
  let B := HolGerm (ComplexModel d × ComplexModel t)
  let e : A ≃ₐ[R] B := {
    toRingEquiv := ambientGermEquiv d t
    commutes' := ambientGermEquiv_tangentPullback d t
  }
  let M : Matrix (Fin a) (Fin b) A := fun i j => germAt 0 (centredMatrix d t F (0,x) i j)
  let N : Matrix (Fin a) (Fin b) B := fun i j => germAt (0,x) (F i j)
  have hEntries : (fun i j => e (M i j)) = N := by
    funext i j
    exact ambientGermEquiv_centred_germ d t (F i j) (0,x) (hF i j)
  let eS := matrixCokernelEquiv (S := R) e M
  rw [hEntries] at eS
  exact (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range M.mulVecLin)).symm.trans
    (eS.trans (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range N.mulVecLin)))

/-- Flatness of the original full product-stalk cokernel gives flatness of
the actual substituted source matrix germ over every finite parameter quotient. -/
theorem original_native_flat_gives_source_matrix_germ_flat
    (d t q : ℕ) {a b : ℕ} (I : Ideal (HolGerm (ComplexModel d)))
    {K : Set (ComplexModel t)} [CompactSpace K]
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (x : ComplexModel t) (hx : x ∈ interior K)
    (hflat : Module.Flat (HolGerm (ComplexModel d))
      ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
        (Matrix.mulVecLin (fun i j => germAt (0,x) (F i j))))) :
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
  have hc : Module.Flat (HolGerm (ComplexModel d))
      ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range
        (Matrix.mulVecLin (fun i j => germAt 0 (centredMatrix d t F (0,x) i j)))) := by
    let := hflat
    exact Module.Flat.of_linearEquiv (centeredNativeMatrixCokernelEquiv d t F x hhol)
  exact original_centered_flat_gives_source_matrix_germ_flat d t q I hO hF hK x hx hc
end
end Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
