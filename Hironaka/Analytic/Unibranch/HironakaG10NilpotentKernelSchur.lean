import Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
import Hironaka.Resolution.HironakaG10LocFrischUniversal

/-!
# Nilpotent finite kernel extensions force the actual Schur obstruction to vanish

The lifted relation-column map is ordinary data obtained from compact
holomorphic relation lifting.  Its comparison operator is proved invertible
internally.  No section-cokernel flatness, ideal-intersection condition or
all-kernel-extension certificate is assumed.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10NilpotentKernelSchur

open Hironaka HironakaG10LocDirectPersistence
  HironakaG10LocProductExact HironakaG10LocFrischLocus HironakaG10LocFrischUniversal
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
  Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible

noncomputable section

/-- A nilpotent parameter-linear perturbation of the reference relation
map has an internally invertible kernel comparison operator. -/
theorem opA_invertible_on_nilpotent_coefficients
    {A E₂ E₁ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (g₀ : E₂ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂)
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) :
    letI := parameterCoefficientModule (E := E₂) b
    letI := parameterCoefficientModule (E := E₁) b
    ∀ (G : (ι → E₂) →L[ℂ] (ι → E₁)) (GA : (ι → E₂) →ₗ[A] (ι → E₁)),
      (∀ x, GA x = G x) →
      (∀ x, GA x - coefficientMap b g₀.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₁))) →
      (opA ((coefficientCLM g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) G).IsInvertible := by
  let := parameterCoefficientModule (E := E₂) b
  let := parameterCoefficientModule (E := E₁) b
  intro G GA hG hmod
  let P : (ι → E₁) →L[ℂ] (ι → E₁) := (coefficientCLM g₀).comp (coefficientCLM R₀)
  let PA : Module.End A (ι → E₁) := coefficientMap b (g₀.comp R₀).toLinearMap
  let RA : (ι → E₁) →ₗ[A] (ι → E₂) := (coefficientMap b R₀.toLinearMap).comp PA
  let R : (ι → E₁) →L[ℂ] (ι → E₂) := (coefficientCLM R₀).comp P
  let uA : Module.End A (ι → E₁) :=
    PA.comp ((coefficientMap b g₀.toLinearMap - GA).comp RA)
  let u : (ι → E₁) →L[ℂ] (ι → E₁) := P.comp (((coefficientCLM g₀) - G).comp R)
  have hPA (x : ι → E₁) : PA x = P x := by
    funext i
    simp [PA, P, coefficientMap_apply]
  have hRA (x : ι → E₁) : RA x = R x := by
    rw [show RA x = coefficientMap b R₀.toLinearMap (PA x) from rfl,
      coefficientCLM_eq_parameterMap b R₀, hPA]
    rfl
  have hu (x : ι → E₁) : uA x = u x := by
    change PA (coefficientMap b g₀.toLinearMap (RA x) - GA (RA x)) = _
    rw [hPA, coefficientCLM_eq_parameterMap b g₀, hG, hRA]
    rfl
  have himage (x : ι → E₁) : uA x ∈ I • (⊤ : Submodule A (ι → E₁)) := by
    have hdiff : coefficientMap b g₀.toLinearMap (RA x) - GA (RA x) ∈
        I • (⊤ : Submodule A (ι → E₁)) := by
      simpa only [neg_sub] using (I • (⊤ : Submodule A (ι → E₁))).neg_mem (hmod (RA x))
    have hmap : (I • (⊤ : Submodule A (ι → E₁))).map PA ≤
        I • (⊤ : Submodule A (ι → E₁)) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    exact hmap (Submodule.mem_map_of_mem hdiff)
  have hinv := isInvertible_id_sub_of_parameter_nilpotent I uA u hu hnil himage
  have heq : (.id ℂ (ι → E₁) - u) = opA P (coefficientCLM R₀) G := by
    ext x i
    simp only [opA_apply, sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply]
    dsimp [u, R, P]
    simp only [sub_apply, coefficientCLM_apply, Pi.sub_apply, map_sub, hR₀]
    abel
  rw [heq] at hinv
  exact hinv

/-- The finite extended relation map internally lifts every vector of
the original kernel projection. -/
theorem projected_kernel_of_nilpotent_extension
    {A E₂ E₁ E₀ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (g₀ : E₂ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂)
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) :
    letI := parameterCoefficientModule (E := E₂) b
    letI := parameterCoefficientModule (E := E₁) b
    ∀ (F : (ι → E₁) →L[ℂ] (ι → E₀))
      (G : (ι → E₂) →L[ℂ] (ι → E₁)) (GA : (ι → E₂) →ₗ[A] (ι → E₁)),
      (∀ x, GA x = G x) →
      (∀ x, GA x - coefficientMap b g₀.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₁))) →
      (∀ x, F (G x) = 0) →
      ∀ x, ∃ y, F y = 0 ∧ coefficientCLM g₀ (coefficientCLM R₀ y) =
        coefficientCLM g₀ (coefficientCLM R₀ x) := by
  let := parameterCoefficientModule (E := E₂) b
  let := parameterCoefficientModule (E := E₁) b
  intro F G GA hG hmod hFG x
  have hA := opA_invertible_on_nilpotent_coefficients b g₀ R₀ hR₀ I hnil G GA hG hmod
  have hR : ∀ e : ι → E₂,
      coefficientCLM g₀ (coefficientCLM R₀ (coefficientCLM g₀ e)) = coefficientCLM g₀ e := by
    intro e
    funext i
    exact hR₀ (e i)
  refine ⟨G (rinv ((coefficientCLM g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) G x),
    hFG _, ?_⟩
  exact P_g_rinv hR hA x

/-- A genuine relation-column extension over a nilpotent parameter test
forces the actual Schur obstruction to vanish, without a flat section
cokernel or a supplied comparison inverse. -/
theorem schurOp_eq_zero_of_nilpotent_kernel_extension
    {A E₂ E₁ E₀ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A)
    (g₀ : E₂ →L[ℂ] E₁) (f₀ : E₁ →L[ℂ] E₀)
    (R₀ : E₁ →L[ℂ] E₂) (S₀ : E₀ →L[ℂ] E₁)
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hcomp : ∀ e, f₀ (g₀ e) = 0)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x)
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) :
    letI := parameterCoefficientModule (E := E₂) b
    letI := parameterCoefficientModule (E := E₁) b
    letI := parameterCoefficientModule (E := E₀) b
    ∀ (F : (ι → E₁) →L[ℂ] (ι → E₀)) (FA : (ι → E₁) →ₗ[A] (ι → E₀))
      (G : (ι → E₂) →L[ℂ] (ι → E₁)) (GA : (ι → E₂) →ₗ[A] (ι → E₁)),
      (∀ x, FA x = F x) → (∀ x, GA x = G x) →
      (∀ x, FA x - coefficientMap b f₀.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₀))) →
      (∀ x, GA x - coefficientMap b g₀.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₁))) →
      (∀ x, F (G x) = 0) →
      schurOp ((coefficientCLM g₀).comp (coefficientCLM R₀))
        ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F = 0 := by
  let := parameterCoefficientModule (E := E₂) b
  let := parameterCoefficientModule (E := E₁) b
  let := parameterCoefficientModule (E := E₀) b
  intro F FA G GA hF hG hmodF hmodG hFG
  have hC := opC_invertible_on_nilpotent_coefficients b g₀ f₀ R₀ S₀ hcomp I hnil F FA hF hmodF
  obtain ⟨hR, hS, _, hExact⟩ := reference_direct_exact_on_coefficients (ι := ι)
    g₀ f₀ R₀ S₀ hR₀ hS₀ hcomp hex
  apply (schurOp_eq_zero_iff hR hS hExact hC).mpr
  exact projected_kernel_of_nilpotent_extension b g₀ R₀ hR₀ I hnil F G GA hG hmodG hFG

end

end Hironaka.Analytic.Unibranch.HironakaG10NilpotentKernelSchur
