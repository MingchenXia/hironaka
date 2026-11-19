import Hironaka.Analytic.Unibranch.HironakaG10CoefficientSchurJet
import Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator

/-! The actual finite coefficient action of Frisch's comparison jet. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpCJet
open Hironaka Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteRank
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-- Coefficient action retains addition of the original whole operator tensors. -/
theorem coefficientTensorOperator_add
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (T S : Γ ⊗[ℂ] (E →L[ℂ] F)) :
    coefficientTensorOperator b (T+S) = coefficientTensorOperator b T + coefficientTensorOperator b S := by
  ext v i
  simp [coefficientTensorOperator]

/-- The original Frisch comparison jet acts on all finite coefficient
vectors as the comparison operator of the actual coefficient action. -/
theorem coefficient_opC_jet
    {Γ E₁ E₀ ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤ RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (F : (ι → E₁) →L[ℂ] (ι → E₀))
    (hF : coefficientTensorOperator b (banachJet d q φ f) = F.toLinearMap) :
    coefficientTensorOperator b (banachJet d q φ (fun z => opC P Q S₀ (f z))) =
      (opC (coefficientCLM P) (coefficientCLM Q) (coefficientCLM S₀) F).toLinearMap := by
  let A := (ContinuousLinearMap.id ℂ E₁ - P).comp S₀
  let B := ContinuousLinearMap.id ℂ E₀ - Q
  have hA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun _ => A) z :=
    Eventually.of_forall fun _ => differentiableAt_const A
  have hFA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun z => (f z).comp A) z :=
    hf.mono fun _ hz => ((ContinuousLinearMap.compL ℂ E₀ E₁ E₀).flip A).differentiableAt.comp _ hz
  have hc : ContDiffAt ℂ ⊤ (fun z => (f z).comp A) 0 :=
    (has_normalized_powerSeriesAt _ hFA).analyticAt.contDiffAt
  have hfun : (fun z => opC P Q S₀ (f z)) = (fun z => (f z).comp A) + (fun _ => B) := by
    funext z
    rfl
  rw [hfun, banachJet_add d q φ _ _ hc contDiffAt_const, coefficientTensorOperator_add,
    banachJet_operator_comp d q φ hφ f (fun _ => A) hf hA, banachJet_const d q φ hφ,
    banachJet_const d q φ hφ, coefficientTensorOperator_comp, coefficientTensorOperator_one,
    coefficientTensorOperator_one, hF]
  ext v i
  simp [opC, A, B, coefficientCLM_apply]
  rw [← Pi.sub_apply, ← map_sub]
  congr 1
end Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpCJet
