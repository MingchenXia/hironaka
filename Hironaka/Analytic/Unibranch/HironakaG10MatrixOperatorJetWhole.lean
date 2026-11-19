import Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetPure
import Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorLinear

/-! # Whole matrix/operator-jet comparison on all finite coefficients -/
set_option autoImplicit false
open Filter Set
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetWhole
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorLinear
  Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetPure
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-- Under the actual pointwise source-germ identification, the entire source
operator jet is the actual Artinian matrix operator on every coefficient
vector, including arbitrary non-pure parameter tensors. -/
theorem matrixOperatorJet_eq_artinian_whole
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
      φ (HolGerm.mk (fun s => ((M s i j : holSubalgebra K) : C(K,ℂ)) z) hg) = F i j z) :
    ∀ v : ι → r → holSubalgebra K,
      parameterTensorEquiv (E := a → holSubalgebra K) b
        (tensorOperator (Γ := Q) (E := r → holSubalgebra K) (F := a → holSubalgebra K)
          (banachJet (E := (r → holSubalgebra K) →L[ℂ] (a → holSubalgebra K)) d q φ
            (fun s => matrixOperator (M s)))
          ((parameterTensorEquiv (E := r → holSubalgebra K) b).symm v)) =
        banachMatrixCLM b hKU F hF v := by
  classical
  letI := parameterCoefficientModule (E := a → holSubalgebra K) b
  letI := parameterCoefficientModule (E := r → holSubalgebra K) b
  let T : Q ⊗[ℂ] ((r → holSubalgebra K) →L[ℂ] (a → holSubalgebra K)) :=
    banachJet d q φ (fun s => matrixOperator (M s))
  let L : (Q ⊗[ℂ] (r → holSubalgebra K)) →ₗ[Q] (ι → a → holSubalgebra K) :=
    (parameterCoefficientLinearEquiv (E := a → holSubalgebra K) b).symm.toLinearMap.comp
      (tensorOperatorLinear T)
  let R : (Q ⊗[ℂ] (r → holSubalgebra K)) →ₗ[Q] (ι → a → holSubalgebra K) :=
    (banachMatrixLinear b hKU F hF).comp
      (parameterCoefficientLinearEquiv (E := r → holSubalgebra K) b).symm.toLinearMap
  have hLR : L = R := by
    apply parameterLinear_ext_one_tmul
    intro w
    change parameterTensorEquiv (E := a → holSubalgebra K) b
      (tensorOperator (Γ := Q) (E := r → holSubalgebra K) (F := a → holSubalgebra K) T
        ((1 : Q) ⊗ₜ[ℂ] w)) =
      banachMatrixCLM b hKU F hF (parameterTensorEquiv b ((1 : Q) ⊗ₜ[ℂ] w))
    exact matrixOperatorJet_eq_artinian_on_one b d q φ hφ M hM F hKU hF hpoint w
  intro v
  have hv := LinearMap.congr_fun hLR (parameterCoefficientLinearEquiv (E := r → holSubalgebra K) b v)
  dsimp only [L,R,LinearMap.comp_apply,tensorOperatorLinear,parameterCoefficientLinearEquiv] at hv
  change parameterTensorEquiv (E := a → holSubalgebra K) b
    (tensorOperator (Γ := Q) (E := r → holSubalgebra K) (F := a → holSubalgebra K) T
      ((parameterTensorEquiv (E := r → holSubalgebra K) b).symm v)) =
    banachMatrixCLM b hKU F hF
      (parameterTensorEquiv b ((parameterTensorEquiv (E := r → holSubalgebra K) b).symm v)) at hv
  simpa only [LinearEquiv.apply_symm_apply] using hv

end Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetWhole
