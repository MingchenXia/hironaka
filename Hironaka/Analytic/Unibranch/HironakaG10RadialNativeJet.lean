import Hironaka.Analytic.Unibranch.HironakaG10RadialSchurLimit
import Hironaka.Analytic.Unibranch.HironakaG10NestedWindowNativeJet

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10RadialNativeJet
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible Hironaka.Analytic.Unibranch.HironakaG10NativeSourceQuotientFlat
  Hironaka.Analytic.Unibranch.HironakaG10InnerFlatSmallSchur Hironaka.Analytic.Unibranch.HironakaG10CompactWindowRestriction
  Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJet
  HironakaG10FlatPolydiscParametric OkaGermBridge
open Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence Hironaka.Analytic.Unibranch.HironakaG10RadialSchurLimit
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

theorem native_quotient_flat_forces_radial_schur_jet
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₂ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₂]
    (hK₂ : K₂ ∈ closedPolydiscs t) (hK₂₀ : K₂ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (F₀ : Fin a → Fin b → holSubalgebra K₂) (G₀ : Fin b → Fin c → holSubalgebra K₂)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin b → holSubalgebra K₂) →L[ℂ] (Fin c → holSubalgebra K₂))
    (S₀ : (Fin a → holSubalgebra K₂) →L[ℂ] (Fin b → holSubalgebra K₂))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : Fin b → Fin c → holSubalgebra K₂)
    (hrel : ∀ z ∈ K₂, ∀ i l, ∑ j, F i j (0,z) * extendZero K₂ (Gr j l) z = 0)
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr)).IsInvertible)
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (sourceOperator d t (K₁ := K₂) hF 0)).IsInvertible)
    (I : Ideal (HolGerm (ComplexModel d)))
    (hflat : ∀ z ∈ K₂, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (0,z) (F i j))))))
    (q : ℕ) (hproper : truncatedParameterIdeal d q I ≠ ⊤) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
    let data := normedComplexAlgebraData Q
    letI : NormedCommRing Q := data.1
    letI : NormedAlgebra ℂ Q := data.2.1
    let basis := Module.finBasis ℂ Q
    coefficientTensorOperator basis (banachJet d q (parameterQuotientMap d q I)
      (fun s => schurOp ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (sourceOperator d t (K₁ := K₂) hF s))) = 0 := by
  let f := sourceOperator d t (K₁ := K₂) hF
  let P := (matrixOperator G₀).comp R₀
  let T := (matrixOperator F₀).comp S₀
  have hK₂O : ∀ z ∈ K₂, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₂₀ hz))
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f s :=
    sourceOperator_holomorphic d t hO hF hK₂O
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
    (parameterQuotientMap_kills d q I) hO hF hK₀ hK₂₀
  have hcoeff : coefficientTensorOperator basis (banachJet d q φ f) =
      (banachMatrixCLM basis hK₂₀ M hM).toLinearMap := by
    have hfun : f = (fun s => matrixOperator (fun i j =>
        HironakaG10FlatPolydiscParametric.restrictParam K₂ (hF i j) s)) := by rfl
    rw [hfun]
    exact hsource
  have hP : coefficientCLM (ι := Fin (Module.finrank ℂ Q)) P =
      (coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀) := by
    ext v i
    rfl
  have hT : coefficientCLM (ι := Fin (Module.finrank ℂ Q)) T =
      (coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀) := by
    ext v i
    rfl
  obtain ⟨hCQ,_⟩ := coefficient_actual_inverse_jet_of_invertible basis d q φ
    (parameterQuotientMap_kills d q I) P T S₀ f hf hC (banachMatrixCLM basis hK₂₀ M hM) hcoeff
  rw [hP,hT] at hCQ
  have hflatQ : ∀ z ∈ K₂, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range (matrixGermMap basis z M)) := by
    intro z hz
    exact quotient_native_flat_gives_source_matrix_germ_flat d t q I hO hF hK₀ z (hK₂₀ hz) (hflat z hz)
  have hrelQ : ∀ z ∈ K₂, ∀ i l, ∑ j, ε (M i j z) * extendZero K₂ (Gr j l) z = 0 := by
    intro z hz i l
    have hsum : (∑ j, ε (M i j z) * extendZero K₂ (Gr j l) z) =
        (∑ j, F i j (0,z) * extendZero K₂ (Gr j l) z) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hres z (hK₂₀ hz) i j]
    exact hsum.trans (hrel z hz i l)
  have hboxData := hK₂
  obtain ⟨ctr,ρ,hρ,hbox⟩ := hboxData
  have hconv : Convex ℝ K₂ := by rw [hbox]; exact closedPolydisc_convex t ctr ρ
  have hc : ctr ∈ interior K₂ := by rw [hbox]; exact closedPolydisc_centre_interior t ctr ρ hρ
  have hSchur := flat_forces_old_schur_zero basis ε hnil t hK₂ hconv hc isOpen_interior hK₂₀
    F₀ G₀ hex R₀ S₀ hR hS Gr M hM hrelQ hflatQ hRef hCQ
  have hfinal := coefficient_actual_schur_jet_of_invertible basis d q φ
    (parameterQuotientMap_kills d q I) P T S₀ f hf hC (banachMatrixCLM basis hK₂₀ M hM) hcoeff
  rw [hP,hT,hSchur] at hfinal
  exact hfinal


theorem native_quotient_flat_forces_radial_scalar_ideal
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₂ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₂]
    (hK₂ : K₂ ∈ closedPolydiscs t) (hK₂₀ : K₂ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O) (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (F₀ : Fin a → Fin b → holSubalgebra K₂) (G₀ : Fin b → Fin c → holSubalgebra K₂)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin b → holSubalgebra K₂) →L[ℂ] (Fin c → holSubalgebra K₂))
    (S₀ : (Fin a → holSubalgebra K₂) →L[ℂ] (Fin b → holSubalgebra K₂))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : Fin b → Fin c → holSubalgebra K₂)
    (hrel : ∀ z ∈ K₂, ∀ i l, ∑ j, F i j (0,z) * extendZero K₂ (Gr j l) z = 0)
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr)).IsInvertible)
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (sourceOperator d t (K₁ := K₂) hF 0)).IsInvertible)
    (hT : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ
      (fun s => schurOp ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (sourceOperator d t (K₁ := K₂) hF s)) s)
    (I : Ideal (HolGerm (ComplexModel d)))
    (hflat : ∀ z ∈ K₂, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (0,z) (F i j)))))) :
    Ideal.span (Set.range fun p : (Fin b → holSubalgebra K₂) ×
        ((Fin a → holSubalgebra K₂) →L[ℂ] ℂ) =>
      let L := p.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₂) p.1)
      HolGerm.mk (L ∘ (fun s => schurOp ((matrixOperator G₀).comp R₀)
        ((matrixOperator F₀).comp S₀) S₀ (sourceOperator d t (K₁ := K₂) hF s)))
        (hT.mono fun _ h => L.differentiableAt.comp _ h)) ≤ I := by
  by_cases hI : I = ⊤
  · rw [hI]
    exact le_top
  apply scalar_operator_ideal_le_of_all_coefficient_actions_zero d I _ hT
  intro q
  have hproper : truncatedParameterIdeal d q I ≠ ⊤ := by
    have hle : truncatedParameterIdeal d q I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) := by
      change I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤ _
      exact sup_le (IsLocalRing.le_maximalIdeal hI) (Ideal.pow_le_self (Nat.succ_ne_zero q))
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle
  exact native_quotient_flat_forces_radial_schur_jet d t hK₂ hK₂₀ hO hF hK₀
    F₀ G₀ hex R₀ S₀ hR hS Gr hrel hRef hC I hflat q hproper

end
end Hironaka.Analytic.Unibranch.HironakaG10RadialNativeJet
