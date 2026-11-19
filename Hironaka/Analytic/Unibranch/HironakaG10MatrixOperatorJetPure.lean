import Hironaka.Analytic.Unibranch.HironakaG10OperatorJetPointEvaluation
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientEvaluationPure
import Hironaka.Analytic.Unibranch.HironakaG10ParameterGermMatrixEvaluation
import Hironaka.Resolution.HironakaG10FlatPolydiscParametric

/-! # Matrix/operator-jet comparison on original pure input vectors -/
set_option autoImplicit false
open Filter Set
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetPure
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetPointEvaluation
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetPointEvaluation
  Hironaka.Analytic.Unibranch.HironakaG10ParameterGermMatrixEvaluation
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientEvaluationPure
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-- For an actual Banach-holomorphic source matrix, whenever the pointwise
original parameter germs have the values of the actual Q-valued matrix F,
the source operator jet and the Artinian matrix operator agree on 1⊗v for
every original Banach input v. -/
theorem matrixOperatorJet_eq_artinian_on_one
    {Q X r a ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] {K U : Set X} [CompactSpace K]
    [Fintype r] [Fintype a] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (M : ComplexModel d → a → r → holSubalgebra K)
    (hM : ∀ i j, ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => M s i j) s)
    (F : a → r → X → Q) (hKU : K ⊆ U) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hpoint : ∀ (z : K) i j, ∃ hg : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => ((M s i j : holSubalgebra K) : C(K,ℂ)) z) s,
      φ (HolGerm.mk (fun s => ((M s i j : holSubalgebra K) : C(K,ℂ)) z) hg) = F i j z)
    (v : r → holSubalgebra K) :
    parameterTensorEquiv (E := a → holSubalgebra K) b
      (tensorOperator (Γ := Q) (E := r → holSubalgebra K) (F := a → holSubalgebra K)
        (banachJet (E := (r → holSubalgebra K) →L[ℂ] (a → holSubalgebra K)) d q φ
          (fun s => matrixOperator (M s))) ((1 : Q) ⊗ₜ[ℂ] v)) =
      banachMatrixCLM b hKU F hF (parameterTensorEquiv b ((1 : Q) ⊗ₜ[ℂ] v)) := by
  classical
  let A : ComplexModel d → ((r → holSubalgebra K) →L[ℂ] (a → holSubalgebra K)) :=
    fun s => matrixOperator (M s)
  have hA : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ A s := by
    filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => hM i j] with s hs
    exact differentiableAt_matrixOperator fun i j => hs i j
  letI := parameterCoefficientModule (E := a → holSubalgebra K) b
  letI := parameterCoefficientModule (E := r → holSubalgebra K) b
  apply coefficientEvaluation_jointly_injective (r := a) b
  intro z
  funext i
  obtain ⟨hav,heval⟩ := coefficientEvaluation_operatorJet_apply_one b d q φ hφ A hA v z i
  have hscalar (j : r) : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => ((M s i j : holSubalgebra K) : C(K,ℂ)) z) s := by
    let L := (ContinuousMap.evalCLM ℂ z).comp (holSubalgebra K).toSubmodule.subtypeL
    exact (hM i j).mono fun _ h => L.differentiableAt.comp _ h
  let h : r → ComplexModel d → ℂ := fun j s => ((M s i j : holSubalgebra K) : C(K,ℂ)) z
  let c : r → ℂ := fun j => ((v j : holSubalgebra K) : C(K,ℂ)) z
  obtain ⟨hs,hsum⟩ := parameter_germ_sum_mul_constants d φ h c hscalar
  have heq : HolGerm.mk (pointCoordinate z i ∘ fun s => A s v)
      (hav.mono fun _ h => (pointCoordinate z i).differentiableAt.comp _ h) =
      HolGerm.mk (fun s => ∑ j, h j s * c j) hs := by
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro s
    simp [pointCoordinate,A,h,c,matrixOperator_apply]
  have hrow : φ (HolGerm.mk (pointCoordinate z i ∘ fun s => A s v)
      (hav.mono fun _ h => (pointCoordinate z i).differentiableAt.comp _ h)) =
      ∑ j, F i j z * algebraMap ℂ Q (c j) := by
    rw [heq,hsum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hg,hgerm⟩ := hpoint z i j
    exact congrArg (fun x : Q => x * algebraMap ℂ Q (c j)) hgerm
  rw [heval,hrow,banachMatrix_evaluation]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficientEvaluation_one_tmul]

end Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetPure
