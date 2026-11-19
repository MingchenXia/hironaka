import Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Parameter-linear extension of complex operators in finite coordinates -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients

noncomputable section

/-- Extend an arbitrary complex-linear map to finite parameter coefficients,
  with the actual transported parameter-algebra actions on both sides. -/
def coefficientMap {A E F ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ A) (f : E →ₗ[ℂ] F) :
    letI := parameterCoefficientModule (E := E) b
    letI := parameterCoefficientModule (E := F) b
    (ι → E) →ₗ[A] (ι → F) := by
  letI := parameterCoefficientModule (E := E) b
  letI := parameterCoefficientModule (E := F) b
  exact (parameterCoefficientLinearEquiv (E := F) b).symm.toLinearMap ∘ₗ
    (f.baseChange A) ∘ₗ (parameterCoefficientLinearEquiv (E := E) b).toLinearMap

/-- The transported parameter-linear operator acts coefficientwise. -/
theorem coefficientMap_apply {A E F ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ A) (f : E →ₗ[ℂ] F)
    (v : ι → E) (i : ι) :
    letI := parameterCoefficientModule (E := E) b
    letI := parameterCoefficientModule (E := F) b
    coefficientMap b f v i = f (v i) := by
  let := parameterCoefficientModule (E := E) b
  let := parameterCoefficientModule (E := F) b
  obtain ⟨z,rfl⟩ := (parameterTensorEquiv (E := E) b).surjective v
  induction z using TensorProduct.induction_on with
  | zero => simp [coefficientMap,parameterCoefficientLinearEquiv]
  | tmul a x => simp [coefficientMap,parameterCoefficientLinearEquiv,
      parameterTensorEquiv_tmul,LinearMap.baseChange_tmul]
  | add z w ihz ihw => simp [map_add,ihz,ihw]

/-- A continuous complex-linear reference operator remains continuous on the
  finite coefficient Banach model while being linear over the parameter algebra. -/
theorem coefficientMap_continuous {A E F ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ A) (f : E →L[ℂ] F) :
    letI := parameterCoefficientModule (E := E) b
    letI := parameterCoefficientModule (E := F) b
    Continuous (coefficientMap b f.toLinearMap) := by
  let := parameterCoefficientModule (E := E) b
  let := parameterCoefficientModule (E := F) b
  apply continuous_pi
  intro i
  have heq : (fun v : ι → E => coefficientMap b f.toLinearMap v i) =
      (fun v : ι → E => f (v i)) := by
    funext v
    exact coefficientMap_apply b f.toLinearMap v i
  rw [heq]
  exact f.continuous.comp (continuous_apply i)

/-- The reference complex Banach operator applied independently to each
  coefficient is a genuine continuous complex-linear map. -/
def coefficientCLM {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Fintype ι]
    (f : E →L[ℂ] F) : (ι → E) →L[ℂ] (ι → F) :=
  ContinuousLinearMap.pi fun i => f.comp (ContinuousLinearMap.proj i)

@[simp] theorem coefficientCLM_apply {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Fintype ι]
    (f : E →L[ℂ] F) (v : ι → E) (i : ι) : coefficientCLM f v i = f (v i) := rfl

/-- The actual coefficientwise Banach operator is simultaneously linear
  for the transported parameter-algebra action. -/
theorem coefficientCLM_eq_parameterMap {A E F ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ A) (f : E →L[ℂ] F) :
    letI := parameterCoefficientModule (E := E) b
    letI := parameterCoefficientModule (E := F) b
    ∀ v, coefficientMap b f.toLinearMap v = coefficientCLM f v := by
  let := parameterCoefficientModule (E := E) b
  let := parameterCoefficientModule (E := F) b
  intro v
  funext i
  exact coefficientMap_apply b f.toLinearMap v i

/-- The reference exactness and both generalized-inverse identities persist
  on the genuine finite coefficient Banach spaces. -/
theorem reference_direct_exact_on_coefficients {E₂ E₁ E₀ ι : Type*}
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Fintype ι]
    (g : E₂ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀)
    (R : E₁ →L[ℂ] E₂) (S : E₀ →L[ℂ] E₁)
    (hR : ∀ e, g (R (g e)) = g e)
    (hS : ∀ x, f (S (f x)) = f x)
    (hcomp : ∀ e, f (g e) = 0)
    (hex : ∀ x, f x = 0 → ∃ e, g e = x) :
    (∀ e : ι → E₂, coefficientCLM g (coefficientCLM R (coefficientCLM g e)) = coefficientCLM g e) ∧
    (∀ x : ι → E₁, coefficientCLM f (coefficientCLM S (coefficientCLM f x)) = coefficientCLM f x) ∧
    (∀ e : ι → E₂, coefficientCLM f (coefficientCLM g e) = 0) ∧
    (∀ x : ι → E₁, coefficientCLM f x = 0 → ∃ e, coefficientCLM g e = x) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro e; funext i; exact hR (e i)
  · intro x; funext i; exact hS (x i)
  · intro e; funext i; exact hcomp (e i)
  · intro x hx
    have hxi (i : ι) : f (x i) = 0 := by
      have h := congrFun hx i
      simpa only [coefficientCLM_apply,Pi.zero_apply] using h
    choose e he using fun i => hex (x i) (hxi i)
    exact ⟨e,funext he⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
