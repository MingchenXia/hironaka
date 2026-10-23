/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.DualitySchemeCharts

/-!
# `deg Ω¹_{X/k} = 2g - 2` for a proper smooth curve with a separable chart pair

Let `k` be algebraically closed and `X` an integral scheme, universally closed and locally of
finite type over `k`, normal, whose modules of differentials over affine opens are torsion free
(e.g. `X` smooth over `k`), with a separable chart pair (`ChartPair.IsSeparable`; on a projective
curve one is constructed from two linear forms, `OmegaDegreeProjective`). Let
`g = p_a(X) = 1 - χ(𝒪_X)` (`CurvesField.Genus.arithmeticGenus`). Then

* `Hⁱ(X, 𝒪_X)` and `Hⁱ(X, Ω¹_{X/k})` are finite-dimensional, and zero for `i ≥ 2`;
* `h⁰(𝒪_X) = 1` (`finrank_cohomology_zero_structure`), so `g = h¹(𝒪_X)`
  (`arithmeticGenus_eq_finrank`);
* `h⁰(Ω¹_{X/k}) = h¹(𝒪_X) = g` (`finrank_cohomology_zero_kaehler`,
  `finrank_cohomology_zero_kaehler_eq_genus`) and `h¹(Ω¹_{X/k}) = h⁰(𝒪_X) = 1`
  (`finrank_cohomology_one_kaehler`, `finrank_cohomology_one_kaehler_eq_one`);
* `deg Ω¹_{X/k} = χ(Ω¹_{X/k}) - χ(𝒪_X) = 2g - 2` (`deg_relativeDifferentials`), with the Euler
  characteristic `eulerCharOf` of a module (cohomology of a chosen finite affine cover).

This is Theorem `thm:sm-omega-degree` of the blueprint for curves with a separable chart pair (the
input of the degree of `ω` on the components of a semistable curve in M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), Thm 1.1,
`references/temkin10-stable-modification/source/semi-stable.tex`, lines 1717–1741).
Blueprint: `sm-omega-degree-scheme.tex`, `thm:sm-omega-degree-scheme`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.StableModification.Omega

namespace DeJongAlterations.StableModification.CurvesField.DualityScheme

noncomputable section

section EulerChar

variable {X : Scheme.{u}} [CompactSpace X]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] {k : Type u} [Field k]

/-- The Euler characteristic `χ(X, F) = ∑ᵢ (-1)ⁱ dim_k Hⁱ(X, F)` of a module (cohomology of the
chosen finite affine cover; `CurvesField.Genus.eulerChar` is the case `F = 𝒪_X`). -/
def eulerCharOf (F : X.Modules) (c : k →+* Γ(X, ⊤)) : ℤ :=
  (cechComplex F (FiniteAffineCover.choose X).U c).homologyEulerChar

lemma eulerCharOf_unit (c : k →+* Γ(X, ⊤)) :
    eulerCharOf (SheafOfModules.unit X.ringCatSheaf) c = Genus.eulerChar X c := rfl

/-- On a scheme covered by two affine opens with affine intersection,
`χ(X, F) = h⁰(F) - h¹(F)` for quasi-coherent `F`. -/
lemma eulerCharOf_eq_of_pair (F : X.Modules) [F.IsQuasicoherent] (c : k →+* Γ(X, ⊤))
    {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) :
    eulerCharOf F c = (finrank k (cohomology F c 0) : ℤ) - finrank k (cohomology F c 1) := by
  unfold eulerCharOf
  rw [Genus.homologyEulerChar_eq_sum _ 2 fun i hi =>
    (ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_pair F c h h₀ h₁ h₀₁ i hi))]
  simp [Finset.sum_range_succ]
  ring

end EulerChar

variable {X : Scheme.{u}} (P : ChartPair X) {k : Type u} [Field k]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [IsAlgClosed k] [UniversallyClosed f]
  [LocallyOfFiniteType f] [CompactSpace X]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  (hnormal : IsNormalScheme X)
  (htf : ∀ U : X.Opens, IsAffineOpen U →
    Module.IsTorsionFree Γ(X, U) Γ(relativeDifferentials f, U))
  (hsep : P.IsSeparable f)

include hnormal htf hsep

/-- `Hⁱ(X, 𝒪_X)` is finite-dimensional. -/
theorem finiteDimensional_cohomology_structure (i : ℕ) :
    FiniteDimensional k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) i) := by
  obtain ⟨h0, h1, -⟩ := P.duality f hnormal htf hsep
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | i + 2 =>
    have := ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_pair
      (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) P.sup_eq_top P.isAffineOpen₀
      P.isAffineOpen₁ P.isAffineOpen_inf (i + 2) (by omega))
    infer_instance

/-- `Hⁱ(X, Ω¹_{X/k})` is finite-dimensional. -/
theorem finiteDimensional_cohomology_kaehler (i : ℕ) :
    FiniteDimensional k (cohomology (relativeDifferentials f) (structureCoeff f) i) := by
  obtain ⟨-, -, h0, h1, -⟩ := P.duality f hnormal htf hsep
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | i + 2 =>
    have := ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_kaehler f P.sup_eq_top
      P.isAffineOpen₀ P.isAffineOpen₁ P.isAffineOpen_inf (i + 2) (by omega))
    infer_instance

/-- **Global functions**: `h⁰(X, 𝒪_X) = 1`. -/
theorem finrank_cohomology_zero_structure :
    finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) = 1 :=
  (P.duality f hnormal htf hsep).2.2.2.2.2.2

/-- **Serre duality, `H⁰` part**: `h⁰(X, Ω¹_{X/k}) = h¹(X, 𝒪_X)`. -/
theorem finrank_cohomology_zero_kaehler :
    finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 0) =
      finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 1) :=
  (P.duality f hnormal htf hsep).2.2.2.2.1

/-- **Serre duality, `H¹` part**: `h¹(X, Ω¹_{X/k}) = h⁰(X, 𝒪_X)`. -/
theorem finrank_cohomology_one_kaehler :
    finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 1) =
      finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) :=
  (P.duality f hnormal htf hsep).2.2.2.2.2.1

/-- The arithmetic genus is `h¹(X, 𝒪_X)`. -/
theorem arithmeticGenus_eq_finrank :
    Genus.arithmeticGenus X (structureCoeff f) =
      finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 1) := by
  have eO : Genus.eulerChar X (structureCoeff f) = _ :=
    eulerCharOf_eq_of_pair (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) P.sup_eq_top
      P.isAffineOpen₀ P.isAffineOpen₁ P.isAffineOpen_inf
  have a2 := finrank_cohomology_zero_structure P f hnormal htf hsep
  rw [Genus.arithmeticGenus, eO]
  omega

/-- **`h⁰(Ω¹_{X/k}) = g`** (blueprint `thm:sm-omega-degree-scheme`). -/
theorem finrank_cohomology_zero_kaehler_eq_genus :
    (finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 0) : ℤ) =
      Genus.arithmeticGenus X (structureCoeff f) := by
  rw [finrank_cohomology_zero_kaehler P f hnormal htf hsep,
    arithmeticGenus_eq_finrank P f hnormal htf hsep]

/-- **`h¹(Ω¹_{X/k}) = 1`** (blueprint `thm:sm-omega-degree-scheme`). -/
theorem finrank_cohomology_one_kaehler_eq_one :
    finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 1) = 1 := by
  rw [finrank_cohomology_one_kaehler P f hnormal htf hsep,
    finrank_cohomology_zero_structure P f hnormal htf hsep]

/-- **`deg Ω¹_{X/k} = 2g - 2`** (blueprint `thm:sm-omega-degree-scheme`): with the degree
`χ(Ω¹_{X/k}) - χ(𝒪_X)` of a line bundle in Riemann–Roch form and `g = p_a(X)`. -/
theorem deg_relativeDifferentials :
    eulerCharOf (relativeDifferentials f) (structureCoeff f) -
        Genus.eulerChar X (structureCoeff f) =
      2 * Genus.arithmeticGenus X (structureCoeff f) - 2 := by
  have eΩ := eulerCharOf_eq_of_pair (relativeDifferentials f) (structureCoeff f) P.sup_eq_top
    P.isAffineOpen₀ P.isAffineOpen₁ P.isAffineOpen_inf
  have eO : Genus.eulerChar X (structureCoeff f) = _ :=
    eulerCharOf_eq_of_pair (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) P.sup_eq_top
      P.isAffineOpen₀ P.isAffineOpen₁ P.isAffineOpen_inf
  have g := arithmeticGenus_eq_finrank P f hnormal htf hsep
  have a0 := finrank_cohomology_zero_kaehler P f hnormal htf hsep
  have a1 := finrank_cohomology_one_kaehler P f hnormal htf hsep
  have a2 := finrank_cohomology_zero_structure P f hnormal htf hsep
  rw [eΩ, eO, g]
  omega

end

end DeJongAlterations.StableModification.CurvesField.DualityScheme
