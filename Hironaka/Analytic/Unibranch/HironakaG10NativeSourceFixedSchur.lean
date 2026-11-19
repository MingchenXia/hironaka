import Hironaka.Analytic.Unibranch.HironakaG10NativeSourceCompactRelations
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianFlatSchur

/-! Uniform exact-start Schur control for the actual original source matrix. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaHolomorphicPointJets
  HironakaRelativeNormalIdeal HironakaG10ArtinianParameterPullback
  HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence
  HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
  Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianFlatSchur
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- The zero-parameter slice is holomorphic on the interior of the original
compact source window. -/
theorem zeroFibre_holomorphic (d t : ℕ) {a b : ℕ}
    {K₀ : Set (ComplexModel t)} {O : Set (ComplexModel d × ComplexModel t)}
    (hO : IsOpen O) {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O) :
    ∀ i j, DifferentiableOn ℂ (fun x => F i j (0,x)) (interior K₀) := by
  intro i j x hx
  have hxO := hK₀ x (interior_subset hx)
  exact ((hF i j (0,x) hxO).differentiableAt (hO.mem_nhds hxO)).comp x
    ((differentiableAt_const (0 : ComplexModel d)).prodMk differentiableAt_id) |>.differentiableWithinAt

/-- Comparison inverses chosen from the original exact fibre control the
literal source matrix over every proper finite parameter quotient. -/
theorem original_native_flat_fixed_schur
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hFG₀ : ∀ x ∈ interior K₀, ∀ i l, ∑ j, F i j (0,x) * G₀ j l x = 0)
    (hex : DirectExact (restrictMatrix K₁ hK₁₀ G₀ hG₀)
      (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x)) (zeroFibre_holomorphic d t hO hF hK₀)))
    (hflat : ∀ z ∈ K₁, Module.Flat (HolGerm (ComplexModel d))
      ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
        (Matrix.mulVecLin (fun i j => germAt (0,z) (F i j))))) :
    ∃ (R₀ : (Fin b → holSubalgebra K₁) →L[ℂ] (Fin c → holSubalgebra K₁))
      (S₀ : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin b → holSubalgebra K₁)),
      (∀ e, matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
        (R₀ (matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀) e)) =
        matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀) e) ∧
      (∀ e, matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀))
        (S₀ (matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
          (zeroFibre_holomorphic d t hO hF hK₀)) e)) =
        matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
          (zeroFibre_holomorphic d t hO hF hK₀)) e) ∧
      ∀ (q : ℕ) (I : Ideal (HolGerm (ComplexModel d)))
        (hproper : truncatedParameterIdeal d q I ≠ ⊤),
        let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
        letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
        let data := normedComplexAlgebraData Q
        letI : NormedCommRing Q := data.1
        letI : NormedAlgebra ℂ Q := data.2.1
        let basis := Module.finBasis ℂ Q
        let ε := quotientResidue d (truncatedParameterIdeal d q I) hproper
        let M := sourceParameterMatrix (K := K₀) basis d q (parameterQuotientMap d q I) hF
        let hM : ∀ i j, DifferentiableOn ℂ (M i j) (interior K₀) := fun i j =>
          differentiableOn_sourceParameterExtension (K := K₀) basis d q (parameterQuotientMap d q I) (hF i j)
        ∃ V, ∃ (_hV : IsOpen V), ∃ (hKV : K₁ ⊆ V), ∃ (hVU : V ⊆ interior K₀),
          ∃ (G : Fin b → Fin c → ComplexModel t → Q)
            (_hG : ∀ j l, DifferentiableOn ℂ (G j l) V),
            (∀ x ∈ V, ∀ i l, ∑ j, M i j x * G j l x = 0) ∧
            (∀ x ∈ V, ∀ j l, ε (G j l x) = G₀ j l x) ∧
            schurOp ((coefficientCLM (matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀))).comp
                (coefficientCLM R₀))
              ((coefficientCLM (matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
                (zeroFibre_holomorphic d t hO hF hK₀)))).comp (coefficientCLM S₀)) (coefficientCLM S₀)
              (banachMatrixCLM basis hKV M (fun i j => (hM i j).mono hVU)) = 0 := by
  obtain ⟨R₀,S₀,hR,hS,huniv⟩ := exists_fixed_flat_artinian_schur t hK₁ isOpen_interior hK₁₀
    (fun i j x => F i j (0,x)) G₀ (zeroFibre_holomorphic d t hO hF hK₀) hG₀ hFG₀ hex
  refine ⟨R₀,S₀,hR,hS,?_⟩
  intro q I hproper
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
  let : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
  let data := normedComplexAlgebraData Q
  let : NormedCommRing Q := data.1
  let : NormedAlgebra ℂ Q := data.2.1
  let basis := Module.finBasis ℂ Q
  let ε := quotientResidue d (truncatedParameterIdeal d q I) hproper
  let M := sourceParameterMatrix (K := K₀) basis d q (parameterQuotientMap d q I) hF
  have hε : ∀ g, ε ((parameterQuotientMap d q I) g) = HolGerm.eval g := by
    intro g
    exact quotientResidue_mk d (truncatedParameterIdeal d q I) hproper g
  have hnil : ∃ m : ℕ, (RingHom.ker ε.toRingHom) ^ m = ⊥ :=
    truncatedResidue_ker_nilpotent d (q+1) I hproper
  obtain ⟨hM,hres⟩ := sourceParameterMatrix_holomorphic_residue basis d q
    (parameterQuotientMap d q I) (parameterQuotientMap_kills d q I) ε hε hO hF hK₀
  have hMflat : ∀ z ∈ K₁, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range (matrixGermMap basis z M)) := by
    intro z hz
    exact original_native_flat_gives_source_matrix_germ_flat d t q I hO hF hK₀ z (hK₁₀ hz) (hflat z hz)
  exact huniv Q _ basis ε hnil M hM hres hMflat
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
