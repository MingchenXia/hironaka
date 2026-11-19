import Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceQuotientJetFlat
import Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientReverse
import Hironaka.Analytic.Unibranch.HironakaG10AllThickeningsFlat
import Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurJetFlat
import Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJetConverse
import Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator
import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
import Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
import Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
import Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceWholeFlat
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJetConverse
  Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurJetFlat
  Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceQuotientJetFlat
  Hironaka.Analytic.Unibranch.HironakaG10SourceQuotientReverse
  Hironaka.Analytic.Unibranch.HironakaG10AllThickeningsFlat
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeHigherRank
  Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra
private theorem truncated_of_proper (d q : ℕ) (I : Ideal (HolGerm (ComplexModel d)))
    (hI : I ≠ ⊤) : truncatedParameterIdeal d q I ≠ ⊤ := by
  have hle : truncatedParameterIdeal d q I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) := by
    change I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤ _
    exact sup_le (IsLocalRing.le_maximalIdeal hI) (Ideal.pow_le_self (Nat.succ_ne_zero q))
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle

theorem varying_scalar_ideal_forces_native_quotient_flat
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (F₀ : Fin a → Fin b → holSubalgebra K₁) (G₀ : Fin b → Fin c → holSubalgebra K₁)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin b → holSubalgebra K₁) →L[ℂ] (Fin c → holSubalgebra K₁))
    (S₀ : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin b → holSubalgebra K₁))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (I : Ideal (HolGerm (ComplexModel d)))
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (sourceOperator d t (K₁ := K₁) hF 0)).IsInvertible)
    (hT : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ
      (fun s => schurOp ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (sourceOperator d t (K₁ := K₁) hF s)) s)
    (hI : Ideal.span (Set.range fun p : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
      let L := p.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) p.1)
      HolGerm.mk (L ∘ (fun s => schurOp ((matrixOperator G₀).comp R₀)
        ((matrixOperator F₀).comp S₀) S₀ (sourceOperator d t (K₁ := K₁) hF s)))
        (hT.mono fun _ h => L.differentiableAt.comp _ h)) ≤ I)
    (hDirect : DirectExact
      (fun j l => kerSec ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
          (zeroFibre_holomorphic d t hO hF hK₀))) (fun j' => G₀ j' l) j)
      (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀))) :
    ∀ z ∈ interior K₁, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (0,z) (F i j))))) := by
  intro z hz
  let R := HolGerm (ComplexModel d)
  let M : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))) :=
    fun i j => germAt 0 (centredMatrix d t F (0,z) i j)
  let C := (Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range M.mulVecLin
  let D := (Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
    (Matrix.mulVecLin (fun i j => germAt (0,z) (F i j)))
  have hz0 : z ∈ interior K₀ := hK₁₀ (interior_subset hz)
  have hhol : ∀ i j, HolAt (F i j) (0,z) := by
    intro i j
    filter_upwards [hO.mem_nhds (hK₀ z (interior_subset hz0))] with x hx
    exact (hF i j x hx).differentiableAt (hO.mem_nhds hx)
  have hc : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] C) := by
    apply matrix_flat_of_all_truncated_flat d t a M I
    intro hproper q
    have hp : truncatedParameterIdeal d q I ≠ ⊤ := truncated_of_proper d q I hproper
    let Q := R ⧸ truncatedParameterIdeal d q I
    let : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
    let data := normedComplexAlgebraData Q
    let : NormedCommRing Q := data.1
    let : NormedAlgebra ℂ Q := data.2.1
    let basis := Module.finBasis ℂ Q
    have hs := varying_scalar_ideal_forces_source_quotient_flat d t hK₁ hK₁₀ hO hF hK₀
      F₀ G₀ hex R₀ S₀ hR hS I q hp hC hT hI hDirect z hz
    have hn : Module.Flat Q (Q ⊗[R] D) :=
      source_matrix_germ_flat_gives_quotient_native_flat d t q I hO hF hK₀ z hz0 hs
    letI := hn
    exact Module.Flat.of_linearEquiv
      ((centeredNativeMatrixCokernelEquiv d t F z hhol).baseChange R Q C D)
  letI := hc
  exact Module.Flat.of_linearEquiv
    ((centeredNativeMatrixCokernelEquiv d t F z hhol).baseChange R (R ⧸ I) C D).symm
end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceWholeFlat
