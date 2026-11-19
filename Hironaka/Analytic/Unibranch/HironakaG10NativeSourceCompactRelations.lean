import Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
import Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue

/-! Compact lifting of original source relations from native matrix-stalk flatness. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeSourceCompactRelations
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange
  HironakaG10ArtinianFlatQuotient HironakaG10FlatPrivilegedEuclidean
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
  Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  OkaRelationSheaf
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- Finitely many original fibre relations lift simultaneously on a common
compact neighborhood, from original native-stalk matrix flatness. -/
theorem original_native_flat_compact_relation_lift
    (d t q : ℕ) {a b c : ℕ} (I : Ideal (HolGerm (ComplexModel d)))
    (hproper : truncatedParameterIdeal d q I ≠ ⊤)
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hrel : ∀ z ∈ K₁, ∀ i l, ∀ᶠ w in 𝓝 z, ∑ j, F i j (0,w) * G₀ j l w = 0)
    (hflat : ∀ z ∈ K₁, Module.Flat (HolGerm (ComplexModel d))
      ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
        (Matrix.mulVecLin (fun i j => germAt (0,z) (F i j))))) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
    let data := normedComplexAlgebraData Q
    letI : NormedCommRing Q := data.1
    letI : NormedAlgebra ℂ Q := data.2.1
    let basis := Module.finBasis ℂ Q
    let ε := quotientResidue d (truncatedParameterIdeal d q I) hproper
    let M := sourceParameterMatrix (K := K₀) basis d q (parameterQuotientMap d q I) hF
    ∃ V, IsOpen V ∧ K₁ ⊆ V ∧ V ⊆ interior K₀ ∧
      ∃ G : Fin b → Fin c → ComplexModel t → Q,
        (∀ j l, DifferentiableOn ℂ (G j l) V) ∧
        (∀ x ∈ V, ∀ i l, ∑ j, M i j x * G j l x = 0) ∧
        ∀ x ∈ V, ∀ j l, ε (G j l x) = G₀ j l x := by
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
  obtain ⟨hM,hres⟩ := sourceParameterMatrix_holomorphic_residue basis d q
    (parameterQuotientMap d q I) (parameterQuotientMap_kills d q I) ε hε hO hF hK₀
  have hMflat : ∀ z ∈ K₁, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range (matrixGermMap basis z M)) := by
    intro z hz
    exact original_native_flat_gives_source_matrix_germ_flat d t q I hO hF hK₀ z (hK₁₀ hz) (hflat z hz)
  have hrel' : ∀ z ∈ K₁, ∀ i l, ∀ᶠ w in 𝓝 z, ∑ j, ε (M i j w) * G₀ j l w = 0 := by
    intro z hz i l
    filter_upwards [hrel z hz i l, isOpen_interior.mem_nhds (hK₁₀ hz)] with w hw hwK
    simpa only [M, hres w hwK] using hw
  exact exists_compact_relation_lift basis ε hK₁ isOpen_interior hK₁₀ M G₀ hM hG₀ hrel' hMflat
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeSourceCompactRelations
