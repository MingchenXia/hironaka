/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OmegaDegreeProjective
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# `deg Ω¹_{X/k} = 2g - 2` for smooth projective normal curves

For a smooth morphism `f : X → S` and affine opens `W ⊆ f⁻¹(V)`, the algebra
`Γ(S, V) → Γ(X, W)` is smooth, so `Ω_{Γ(X, W)/Γ(S, V)} ≅ Γ(Ω¹_{X/S}, W)` is a projective, hence
flat, hence torsion-free `Γ(X, W)`-module (`isTorsionFree_sections_of_smooth`). This discharges
the torsion-freeness hypothesis of `OmegaDegreeProjective` for smooth curves:
for `k` algebraically closed and `X` integral, normal, smooth and projective over `k`, of
dimension at most one and not a point, with `g = p_a(X)`,
`h⁰(Ω¹_{X/k}) = g`, `h¹(Ω¹_{X/k}) = 1` and `deg Ω¹_{X/k} = 2g - 2` (`omegaDegree_of_smooth`).

The normality hypothesis is kept: "smooth over a field implies normal" is not available in
Mathlib (blueprint `sm-omega-degree-scheme.tex`, `rem:sm-omega-degree-scheme-literature`).
This is Theorem `thm:sm-omega-degree` of the blueprint (`cor:sm-omega-degree-projective`), the
degree input of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Thm 1.1 (`references/temkin10-stable-modification/source/semi-stable.tex`,
lines 1717–1741).
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.StableModification.Omega

namespace DeJongAlterations.StableModification.CurvesField.DualityScheme

/-- **Differentials of a smooth morphism are torsion free on affine opens**: for `f : X → S`
smooth and affine opens `W ⊆ f⁻¹(V)`, `Γ(Ω¹_{X/S}, W)` is a torsion-free `Γ(X, W)`-module. -/
theorem isTorsionFree_sections_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    {W : X.Opens} (hW : IsAffineOpen W) {V : S.Opens} (hV : IsAffineOpen V)
    (hWV : W ≤ f ⁻¹ᵁ V) : Module.IsTorsionFree Γ(X, W) Γ(relativeDifferentials f, W) := by
  let : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have hs : Algebra.Smooth Γ(S, V) Γ(X, W) := f.smooth_appLE hV hW hWV
  have : Module.IsTorsionFree Γ(X, W) Ω[Γ(X, W)⁄Γ(S, V)] := inferInstance
  have : Module.IsTorsionFree Γ(X, W) (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) :=
    this
  exact (sectionsEquiv f hW hV hWV).symm.injective.moduleIsTorsionFree _
    (map_smul (sectionsEquiv f hW hV hWV).symm)

/-- Over an affine base, differentials of a smooth morphism are torsion free on every affine
open (the hypothesis `htf` of `OmegaDegree` and `OmegaDegreeProjective`). -/
theorem isTorsionFree_sections_of_smooth' {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsTorsionFree Γ(X, U) Γ(relativeDifferentials f, U) :=
  isTorsionFree_sections_of_smooth f hU (isAffineOpen_top _) (le_preimage_top f U)

variable {X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
  [IsIntegral X] [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  [Smooth f]

/-- **`deg Ω¹_{X/k} = 2g - 2` for a smooth normal projective curve** (blueprint
`thm:sm-omega-degree`, `cor:sm-omega-degree-projective`): `h⁰(𝒪_X) = 1`, `h⁰(Ω¹_{X/k}) = g`,
`h¹(Ω¹_{X/k}) = 1` and `χ(Ω¹_{X/k}) - χ(𝒪_X) = 2g - 2`, with `g = p_a(X)`. -/
theorem omegaDegree_of_smooth (hp : IsProjectiveOver f) (hdim : topologicalKrullDim X ≤ 1)
    (hpt : ∃ x : X, x ≠ genericPoint X) (hnormal : IsNormalScheme X) :
    finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) = 1 ∧
      (finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 0) : ℤ) =
        Genus.arithmeticGenus X (structureCoeff f) ∧
      finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 1) = 1 ∧
      eulerCharOf (relativeDifferentials f) (structureCoeff f) -
          Genus.eulerChar X (structureCoeff f) =
        2 * Genus.arithmeticGenus X (structureCoeff f) - 2 :=
  have htf := isTorsionFree_sections_of_smooth' f
  ⟨finrank_cohomology_zero_structure_of_isProjectiveOver f hp hdim hpt hnormal htf,
    finrank_cohomology_zero_kaehler_eq_genus_of_isProjectiveOver f hp hdim hpt hnormal htf,
    finrank_cohomology_one_kaehler_eq_one_of_isProjectiveOver f hp hdim hpt hnormal htf,
    deg_relativeDifferentials_of_isProjectiveOver f hp hdim hpt hnormal htf⟩

end DeJongAlterations.StableModification.CurvesField.DualityScheme
