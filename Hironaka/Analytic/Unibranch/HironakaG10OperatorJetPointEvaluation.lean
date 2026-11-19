import Hironaka.Analytic.Unibranch.HironakaG10OperatorJetEvaluation
import Hironaka.Analytic.Unibranch.HironakaG10BanachJetPointEvaluation

/-! # Pointwise identification of actual operator jets in finite coefficients -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10OperatorJetPointEvaluation
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetEvaluation
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetPointEvaluation
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-- At an actual point and output coordinate, the coefficient evaluation of
the operator jet acting on a constant input is the original scalar parameter
germ evaluated by the same quotient map. -/
theorem coefficientEvaluation_operatorJet_apply_one
    {Q X r a ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [CompactSpace K] [Fintype r] [Fintype a]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (A : ComplexModel d → ((r → holSubalgebra K) →L[ℂ] (a → holSubalgebra K)))
    (hA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ A z)
    (v : r → holSubalgebra K) (z : K) (i : a) :
    letI := parameterCoefficientModule (E := a → holSubalgebra K) b
    ∃ hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => A s v) s,
      coefficientEvaluation b z
        (parameterTensorEquiv (E := a → holSubalgebra K) b
          (tensorOperator (Γ := Q) (E := r → holSubalgebra K) (F := a → holSubalgebra K)
            (banachJet (E := (r → holSubalgebra K) →L[ℂ] (a → holSubalgebra K)) d q φ A)
            ((1 : Q) ⊗ₜ[ℂ] v))) i =
        φ (HolGerm.mk (pointCoordinate z i ∘ fun s => A s v)
          (hf.mono fun _ h => (pointCoordinate z i).differentiableAt.comp _ h)) := by
  let _ := parameterCoefficientModule (E := a → holSubalgebra K) b
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => A s v) s :=
    hA.mono fun _ h => h.clm_apply (differentiableAt_const v)
  refine ⟨hf,?_⟩
  rw [operatorJet_apply_one d q φ A hA v]
  exact coefficientEvaluation_banachJet_eq_original b d q φ hφ (fun s => A s v) hf z i

end Hironaka.Analytic.Unibranch.HironakaG10OperatorJetPointEvaluation
