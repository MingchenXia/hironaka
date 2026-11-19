/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.StableModification.CurvesField.CohomologyP1

/-!
# The vanishing `H¹(𝒪_Y(m Σ pᵢ)) = 0` in Temkin's Proposition 4.4.6 (corrected)

Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Prop. 4.4.6
(`references/temkin10-stable-modification/source/semi-stable.tex`, lines 3204–3214): `Y = C'_s` is
the closed fibre of a semistable curve, `Z ≅ ℙ¹` an exceptional component meeting the union `Y'`
of the other components transversally in `∂Z` (at most two points), and `pᵢ ∈ Y' ∖ Z` smooth
points, one on each component of `Y'`. Temkin asserts that `h¹(Z, 𝒪_Z) = 0` gives
`H¹(𝒪_Y(m Σ pᵢ)) = 0` for `m ≫ 0`. As recorded in `ERRATA.md` (T10), this fails as stated
when `|∂Z| = 2`, since then the relevant group is `H¹(ℙ¹, 𝒪(-2)) ≠ 0`; the correct argument uses
the exact sequence `0 → 𝒪_Z(-∂Z) → 𝒪_Y(m Σ pᵢ) → 𝒪_{Y'}(m Σ pᵢ) → 0` and needs, besides
`H¹(Y', 𝒪_{Y'}(m Σ pᵢ)) = 0` (Serre vanishing on `Y'`, `RiemannRoch.serre_vanishing`), that the
connecting map `H⁰(Y', 𝒪_{Y'}(m Σ pᵢ)) → H¹(Z, 𝒪_Z(-∂Z))` be onto. Since
`h¹(ℙ¹, 𝒪(-e)) = max(e - 1, 0) ≤ 1` for `e ≤ 2` (`P1Charts.finrank_H1`), it is onto as soon as
some section over `Y'` does not extend to `Y`, i.e. separates the two points of `∂Z`.

This file proves the cohomological core of that argument for an arbitrary short exact sequence of
quasi-coherent modules (blueprint `sm-curves-fields-cohomology.tex`, `lem:sm-temkin-vanishing`).

## Main results

* `isZero_cohomology_one_of_surjective_δ`: `H¹(F₃) = 0` and `δ : H⁰(F₃) → H¹(F₁)` onto give
  `H¹(F₂) = 0`.
* `isZero_cohomology_one_of_isZero`: `H¹(F₁) = H¹(F₃) = 0` give `H¹(F₂) = 0` (the cases
  `|∂Z| ≤ 1`).
* `surjective_δ_of_finrank_le_one`: over a field, if `dim H¹(F₁) ≤ 1` and
  `H⁰(F₂) → H⁰(F₃)` is not onto, then `δ` is onto (the case `|∂Z| = 2`).
* `isZero_cohomology_one_temkin`: the combination used in Prop. 4.4.6.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Hironaka.StableModification.Cohomology

namespace Hironaka.StableModification.CurvesField

noncomputable section

variable {Y : Scheme.{u}} [CompactSpace Y]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  (S : ShortComplex Y.Modules) (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

section Ring

variable {R : Type u} [CommRing R] (c : R →+* Γ(Y, ⊤))

include hS in
/-- If `H¹(F₃) = 0` and the connecting map `H⁰(F₃) → H¹(F₁)` is onto, then `H¹(F₂) = 0`. -/
theorem isZero_cohomology_one_of_surjective_δ (h₃ : Limits.IsZero (cohomology S.X₃ c 1))
    (hδ : Function.Surjective (cohomologyδ c S hS 0)) : Limits.IsZero (cohomology S.X₂ c 1) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h₃ ⊢
  refine ⟨fun x x' => ?_⟩
  suffices h : ∀ x : cohomology S.X₂ c 1, x = 0 by rw [h x, h x']
  intro x
  have e₂ := (ShortComplex.moduleCat_exact_iff _).mp (cohomology_exact₂ c S hS 1)
  have e₁ := cohomology_exact₁ c S hS 0
  obtain ⟨y, rfl⟩ := e₂ x (Subsingleton.elim _ _)
  obtain ⟨z, rfl⟩ := hδ y
  have hmem : (cohomologyδ c S hS 0).hom z ∈ LinearMap.range (cohomologyδ c S hS 0).hom :=
    ⟨z, rfl⟩
  rw [e₁.moduleCat_range_eq_ker] at hmem
  exact hmem

include hS in
/-- If `H¹(F₁) = H¹(F₃) = 0` then `H¹(F₂) = 0`. -/
theorem isZero_cohomology_one_of_isZero (h₁ : Limits.IsZero (cohomology S.X₁ c 1))
    (h₃ : Limits.IsZero (cohomology S.X₃ c 1)) : Limits.IsZero (cohomology S.X₂ c 1) := by
  refine isZero_cohomology_one_of_surjective_δ S hS c h₃ fun y => ⟨0, ?_⟩
  rw [ModuleCat.isZero_iff_subsingleton] at h₁
  exact Subsingleton.elim _ _

end Ring

section Field

variable {K : Type u} [Field K] (c : K →+* Γ(Y, ⊤))

include hS in
/-- Over a field: if `dim H¹(F₁) ≤ 1` and `H⁰(F₂) → H⁰(F₃)` is not onto, then the connecting map
`H⁰(F₃) → H¹(F₁)` is onto. -/
theorem surjective_δ_of_finrank_le_one [FiniteDimensional K (cohomology S.X₁ c 1)]
    (h₁ : Module.finrank K (cohomology S.X₁ c 1) ≤ 1)
    (hg : ¬ Function.Surjective (cohomologyMap c S.g 0)) :
    Function.Surjective (cohomologyδ c S hS 0) := by
  have e₃ := (ShortComplex.moduleCat_exact_iff _).mp (cohomology_exact₃ c S hS 0)
  -- some class is not in the image of `H⁰(F₂)`, so it has nonzero image under `δ`
  have hne : LinearMap.range (cohomologyδ c S hS 0).hom ≠ ⊥ := by
    intro hbot
    apply hg
    intro z
    have hz : (cohomologyδ c S hS 0) z = 0 := by
      have : (cohomologyδ c S hS 0).hom z ∈ LinearMap.range (cohomologyδ c S hS 0).hom := ⟨z, rfl⟩
      rw [hbot] at this
      exact this
    exact e₃ z hz
  have hpos : 1 ≤ Module.finrank K (LinearMap.range (cohomologyδ c S hS 0).hom) :=
    Submodule.one_le_finrank_iff.mpr hne
  have h₁' : Module.finrank K (cohomology S.X₁ c (0 + 1)) ≤ 1 := h₁
  have : FiniteDimensional K (cohomology S.X₁ c (0 + 1)) :=
    inferInstanceAs (FiniteDimensional K (cohomology S.X₁ c 1))
  have htop : LinearMap.range (cohomologyδ c S hS 0).hom = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.range (cohomologyδ c S hS 0).hom)
    omega
  exact LinearMap.range_eq_top.mp htop

include hS in
/-- **The corrected vanishing of Temkin, Prop. 4.4.6** (ERRATA T10; blueprint
`lem:sm-temkin-vanishing`). Let `0 → F₁ → F₂ → F₃ → 0` be exact with `F₂`, `F₃`
quasi-coherent (in Temkin's case `F₁ = 𝒪_Z(-∂Z)`, `F₂ = 𝒪_Y(m Σ pᵢ)`, `F₃ = 𝒪_{Y'}(m Σ pᵢ)`),
`H¹(F₃) = 0` and `dim H¹(F₁) ≤ 1` (`F₁ ≅ 𝒪_{ℙ¹}(-e)`, `e = |∂Z| ≤ 2`). If either `H¹(F₁) = 0`
(`e ≤ 1`) or some global section of `F₃` does not lift to `F₂` (for `e = 2`: a section of
`𝒪_{Y'}(m Σ pᵢ)` with different values at the two points of `∂Z`), then `H¹(F₂) = 0`. -/
theorem isZero_cohomology_one_temkin [FiniteDimensional K (cohomology S.X₁ c 1)]
    (h₁ : Module.finrank K (cohomology S.X₁ c 1) ≤ 1) (h₃ : Limits.IsZero (cohomology S.X₃ c 1))
    (hsep : Limits.IsZero (cohomology S.X₁ c 1) ∨ ¬ Function.Surjective (cohomologyMap c S.g 0)) :
    Limits.IsZero (cohomology S.X₂ c 1) := by
  rcases hsep with h | h
  · exact isZero_cohomology_one_of_isZero S hS c h h₃
  · exact isZero_cohomology_one_of_surjective_δ S hS c h₃
      (surjective_δ_of_finrank_le_one S hS c h₁ h)

end Field

end

end Hironaka.StableModification.CurvesField
