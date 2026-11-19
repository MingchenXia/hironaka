import Hironaka.Algebra.FunctionFieldDimension

/-!
# Actual dimension forces an original polynomial coordinate equation
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k A : Type u) [Field k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- Original finite-type dimension rules out injectivity of an actual excess-coordinate map. -/
theorem not_injective_of_dimension_lt {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ k →ₐ[k] A) (hdim : ringKrullDim A < Fintype.card σ) :
    ¬ Function.Injective f := by
  intro hf
  let K := FractionRing A
  obtain ⟨d, hd, htr⟩ := FunctionFieldDimension.exists_dimension_and_trdeg k A K
  let g : MvPolynomial σ k →ₐ[k] K := (IsScalarTower.toAlgHom k A K).comp f
  have hg : Function.Injective g := (IsFractionRing.injective A K).comp hf
  have h := lift_trdeg_le_of_injective g hg
  rw [htr] at h
  have hcard : Fintype.card σ ≤ d := by simpa using h
  rw [hd] at hdim
  exact (not_lt_of_ge (show (Fintype.card σ : WithBot ℕ∞) ≤ d from by exact_mod_cast hcard)) hdim

/-- An actual nonzero original relation is produced from the original dimension inequality. -/
theorem exists_nonzero_relation_of_dimension_lt {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ k →ₐ[k] A) (hdim : ringKrullDim A < Fintype.card σ) :
    ∃ F : MvPolynomial σ k, F ≠ 0 ∧ f F = 0 := by
  have h := not_injective_of_dimension_lt k A f hdim
  change ¬ (∀ P Q, f P = f Q → P = Q) at h
  push Not at h
  obtain ⟨P, Q, heq, hne⟩ := h
  refine ⟨P - Q, sub_ne_zero.mpr hne, ?_⟩
  simp only [map_sub, heq, sub_self]

end Hironaka.Algebra.ProjectiveSecant
