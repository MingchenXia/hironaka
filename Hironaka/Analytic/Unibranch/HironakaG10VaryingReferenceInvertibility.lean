import Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
import Hironaka.Analytic.Unibranch.HironakaG10NilpotentInvertiblePerturbation
import Hironaka.Resolution.HironakaG10LocFrischUniversal

/-!
# Nilpotent finite kernel extensions force the actual Schur obstruction to vanish

The lifted relation-column map is ordinary data obtained from compact
holomorphic relation lifting.  Its comparison operator is proved invertible
internally.  No section-cokernel flatness, ideal-intersection condition or
all-kernel-extension certificate is assumed.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingReferenceInvertibility

open Hironaka HironakaG10LocDirectPersistence
  HironakaG10LocProductExact HironakaG10LocFrischLocus HironakaG10LocFrischUniversal
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
  Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
  Hironaka.Analytic.Unibranch.HironakaG10NilpotentInvertiblePerturbation

noncomputable section

/-- A nilpotent parameter-linear perturbation of the reference relation
map has an internally invertible kernel comparison operator. -/
theorem opA_invertible_of_invertible_reference
    {A E₂ E₁ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (g₀ : E₂ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂)
    (gr : E₂ →L[ℂ] E₁) (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) :
    letI := parameterCoefficientModule (E := E₂) b
    letI := parameterCoefficientModule (E := E₁) b
    ∀ (G : (ι → E₂) →L[ℂ] (ι → E₁)) (GA : (ι → E₂) →ₗ[A] (ι → E₁)),
      (∀ x, GA x = G x) →
      ∀ (_hBase : (opA ((coefficientCLM (ι := ι) g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) (coefficientCLM gr)).IsInvertible)
        (BInvA : Module.End A (ι → E₁)),
      (∀ x, BInvA x = (opA ((coefficientCLM (ι := ι) g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) (coefficientCLM gr)).inverse x) →
      (∀ x, GA x - coefficientMap b gr.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₁))) →
      (opA ((coefficientCLM g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) G).IsInvertible := by
  let := parameterCoefficientModule (E := E₂) b
  let := parameterCoefficientModule (E := E₁) b
  intro G GA hG hBase BInvA hInv hmod
  let P : (ι → E₁) →L[ℂ] (ι → E₁) := (coefficientCLM g₀).comp (coefficientCLM R₀)
  let PA : Module.End A (ι → E₁) := coefficientMap b (g₀.comp R₀).toLinearMap
  let RA : (ι → E₁) →ₗ[A] (ι → E₂) := (coefficientMap b R₀.toLinearMap).comp PA
  let R : (ι → E₁) →L[ℂ] (ι → E₂) := (coefficientCLM R₀).comp P
  let uA : Module.End A (ι → E₁) :=
    PA.comp ((coefficientMap b gr.toLinearMap - GA).comp RA)
  let u : (ι → E₁) →L[ℂ] (ι → E₁) := P.comp (((coefficientCLM gr) - G).comp R)
  have hPA (x : ι → E₁) : PA x = P x := by
    funext i
    simp [PA, P, coefficientMap_apply]
  have hRA (x : ι → E₁) : RA x = R x := by
    rw [show RA x = coefficientMap b R₀.toLinearMap (PA x) from rfl,
      coefficientCLM_eq_parameterMap b R₀, hPA]
    rfl
  have hu (x : ι → E₁) : uA x = u x := by
    change PA (coefficientMap b gr.toLinearMap (RA x) - GA (RA x)) = _
    rw [hPA, coefficientCLM_eq_parameterMap b gr, hG, hRA]
    rfl
  have himage (x : ι → E₁) : uA x ∈ I • (⊤ : Submodule A (ι → E₁)) := by
    have hdiff : coefficientMap b gr.toLinearMap (RA x) - GA (RA x) ∈
        I • (⊤ : Submodule A (ι → E₁)) := by
      simpa only [neg_sub] using (I • (⊤ : Submodule A (ι → E₁))).neg_mem (hmod (RA x))
    have hmap : (I • (⊤ : Submodule A (ι → E₁))).map PA ≤
        I • (⊤ : Submodule A (ι → E₁)) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    exact hmap (Submodule.mem_map_of_mem hdiff)
  let B : (ι → E₁) →L[ℂ] (ι → E₁) := opA P (coefficientCLM R₀) (coefficientCLM gr)
  have hinv := invertible_sub_nilpotent_parameter_perturbation I B hBase BInvA hInv uA u hu hnil himage
  have heq : B - u = opA P (coefficientCLM R₀) G := by
    ext x i
    simp only [opA_apply, sub_apply, Pi.sub_apply]
    dsimp [B, u, R]
    simp only [opA_apply, sub_apply, Pi.sub_apply, Pi.add_apply, map_sub]
    abel
  rw [heq] at hinv
  exact hinv


end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingReferenceInvertibility
