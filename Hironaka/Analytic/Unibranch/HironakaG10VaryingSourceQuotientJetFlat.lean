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
namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceQuotientJetFlat
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
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
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

theorem varying_scalar_ideal_forces_source_quotient_flat
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
    (I : Ideal (HolGerm (ComplexModel d))) (q : ℕ)
    (hproper : truncatedParameterIdeal d q I ≠ ⊤)
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
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
    let data := normedComplexAlgebraData Q
    letI : NormedCommRing Q := data.1
    letI : NormedAlgebra ℂ Q := data.2.1
    let basis := Module.finBasis ℂ Q
    let M := sourceParameterMatrix (K := K₀) basis d q (parameterQuotientMap d q I) hF
    ∀ z ∈ interior K₁, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range (matrixGermMap basis z M)) := by
  let f := sourceOperator d t (K₁ := K₁) hF
  let P := (matrixOperator G₀).comp R₀
  let T := (matrixOperator F₀).comp S₀
  have hK₁O : ∀ z ∈ K₁, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₁₀ hz))
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f s :=
    sourceOperator_holomorphic d t hO hF hK₁O
  have hf0 := sourceOperator_zero d t hK₁₀ hO hF hK₀
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
  let : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
  let data := normedComplexAlgebraData Q
  let : NormedCommRing Q := data.1
  let : NormedAlgebra ℂ Q := data.2.1
  let basis := Module.finBasis ℂ Q
  let φ := parameterQuotientMap d q I
  let ε := quotientResidue d (truncatedParameterIdeal d q I) hproper
  let M := sourceParameterMatrix (K := K₀) basis d q φ hF
  have hε : ∀ g, ε (φ g) = HolGerm.eval g := by
    intro g
    exact quotientResidue_mk d (truncatedParameterIdeal d q I) hproper g
  have hnil : ∃ m : ℕ, (RingHom.ker ε.toRingHom) ^ m = ⊥ :=
    truncatedResidue_ker_nilpotent d (q+1) I hproper
  obtain ⟨hM,hres⟩ := sourceParameterMatrix_holomorphic_residue basis d q φ
    (parameterQuotientMap_kills d q I) ε hε hO hF hK₀
  obtain ⟨_,hsource⟩ := sourceCoefficientOperator_eq_artinian basis d q φ
    (parameterQuotientMap_kills d q I) hO hF hK₀ hK₁₀
  have hcoeff : coefficientTensorOperator basis (banachJet d q φ f) =
      (banachMatrixCLM basis hK₁₀ M hM).toLinearMap := by
    have hfun : f = (fun s => matrixOperator (fun i j =>
        HironakaG10FlatPolydiscParametric.restrictParam K₁ (hF i j) s)) := by rfl
    rw [hfun]
    exact hsource
  have hjet : banachJet d q φ (fun s => schurOp P T S₀ (f s)) = 0 :=
    banachJet_zero_of_scalar_operator_ideal_le d I _ hT hI q
  exact varying_schur_jet_zero_forces_matrix_flat (Q := Q) (ι := Fin (Module.finrank ℂ Q))
    hK₁ isOpen_interior hK₁₀ F₀ G₀ hex R₀ S₀ hR hS d q φ (parameterQuotientMap_kills d q I)
    basis ε hnil M hM (fun i j x => F i j (0,x)) (zeroFibre_holomorphic d t hO hF hK₀)
    hres f hf hf0 hC hcoeff hjet hDirect
end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceQuotientJetFlat
