import Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-! # Original pointwise germs and the Artinian coefficient evaluation -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachJetPointEvaluation
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-- Point evaluation followed by a vector coordinate is continuous on the
actual finite product of the polydisc Banach algebra. -/
noncomputable def pointCoordinate {X r : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [CompactSpace K] [Fintype r] (z : K) (j : r) :
    (r → holSubalgebra K) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp
    ((holSubalgebra K).toSubmodule.subtypeL.comp (ContinuousLinearMap.proj j))

/-- The finite coefficient evaluation used by the Artinian matrix action is
precisely the given quotient map applied to the original pointwise germ. -/
theorem coefficientEvaluation_banachJet_eq_original
    {Q X r ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [CompactSpace K] [Fintype r]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (f : ComplexModel d → (r → holSubalgebra K))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (z : K) (j : r) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    coefficientEvaluation b z (parameterTensorEquiv b (banachJet d q φ f)) j =
      φ (HolGerm.mk (pointCoordinate z j ∘ f)
        (hf.mono fun _ h => (pointCoordinate z j).differentiableAt.comp _ h)) := by
  letI := parameterCoefficientModule (E := r → holSubalgebra K) b
  rw [coefficientEvaluation_apply]
  symm
  simpa [pointCoordinate] using
    scalar_germ_eq_coefficient_jet b d q φ hφ f hf (pointCoordinate z j)

end Hironaka.Analytic.Unibranch.HironakaG10BanachJetPointEvaluation
