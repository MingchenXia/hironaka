/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OmegaDegree
import DeJongAlterations.StableModification.CurvesField.DualitySchemeExistence

/-!
# `deg Ω¹_{X/k} = 2g - 2` for normal projective curves

Let `k` be algebraically closed and `X` an integral, normal scheme, projective over `k`
(`IsProjectiveOver`), of topological dimension at most one and not a point, whose modules of
differentials over affine opens are torsion free (e.g. `X` smooth over `k`). Then with
`g = p_a(X) = 1 - χ(𝒪_X)`:

* `h⁰(X, 𝒪_X) = 1` (`finrank_cohomology_zero_structure_of_isProjectiveOver`);
* `h⁰(X, Ω¹_{X/k}) = g` (`finrank_cohomology_zero_kaehler_eq_genus_of_isProjectiveOver`);
* `h¹(X, Ω¹_{X/k}) = 1` (`finrank_cohomology_one_kaehler_eq_one_of_isProjectiveOver`);
* `deg Ω¹_{X/k} = χ(Ω¹_{X/k}) - χ(𝒪_X) = 2g - 2` (`deg_relativeDifferentials_of_isProjectiveOver`).

This is Theorem `thm:sm-omega-degree` of the blueprint (`sm-omega-degree-scheme.tex`,
`cor:sm-omega-degree-projective`): the separable chart pair of `exists_isSeparable_chartPair`
fed into the chart-pair theorems of `OmegaDegree`. It is the degree input of the ampleness
half of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
Thm 1.1 (`references/temkin10-stable-modification/source/semi-stable.tex`, lines 1717–1741).
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.StableModification.Omega

namespace DeJongAlterations.StableModification.CurvesField.DualityScheme

variable {X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
  [IsIntegral X] [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  (hp : IsProjectiveOver f) (hdim : topologicalKrullDim X ≤ 1)
  (hpt : ∃ x : X, x ≠ genericPoint X) (hnormal : IsNormalScheme X)
  (htf : ∀ U : X.Opens, IsAffineOpen U →
    Module.IsTorsionFree Γ(X, U) Γ(relativeDifferentials f, U))

include hp hdim hpt hnormal htf

/-- **`h⁰(𝒪_X) = 1`** for a normal projective curve. -/
theorem finrank_cohomology_zero_structure_of_isProjectiveOver :
    finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) = 1 := by
  have := hp.isProper
  obtain ⟨P, hP⟩ := exists_isSeparable_chartPair f hp hdim hpt
  exact finrank_cohomology_zero_structure P f hnormal htf hP

/-- **`h⁰(Ω¹_{X/k}) = g`** for a normal projective curve (blueprint
`cor:sm-omega-degree-projective`). -/
theorem finrank_cohomology_zero_kaehler_eq_genus_of_isProjectiveOver :
    (finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 0) : ℤ) =
      Genus.arithmeticGenus X (structureCoeff f) := by
  have := hp.isProper
  obtain ⟨P, hP⟩ := exists_isSeparable_chartPair f hp hdim hpt
  exact finrank_cohomology_zero_kaehler_eq_genus P f hnormal htf hP

/-- **`h¹(Ω¹_{X/k}) = 1`** for a normal projective curve. -/
theorem finrank_cohomology_one_kaehler_eq_one_of_isProjectiveOver :
    finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 1) = 1 := by
  have := hp.isProper
  obtain ⟨P, hP⟩ := exists_isSeparable_chartPair f hp hdim hpt
  exact finrank_cohomology_one_kaehler_eq_one P f hnormal htf hP

/-- **`deg Ω¹_{X/k} = 2g - 2`** for a normal projective curve (blueprint `thm:sm-omega-degree`,
`cor:sm-omega-degree-projective`). -/
theorem deg_relativeDifferentials_of_isProjectiveOver :
    eulerCharOf (relativeDifferentials f) (structureCoeff f) -
        Genus.eulerChar X (structureCoeff f) =
      2 * Genus.arithmeticGenus X (structureCoeff f) - 2 := by
  have := hp.isProper
  obtain ⟨P, hP⟩ := exists_isSeparable_chartPair f hp hdim hpt
  exact deg_relativeDifferentials P f hnormal htf hP

/-- The cohomology of `𝒪_X` and of `Ω¹_{X/k}` of a normal projective curve is finite-dimensional
in every degree. -/
theorem finiteDimensional_cohomology_of_isProjectiveOver (i : ℕ) :
    FiniteDimensional k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) i) ∧
      FiniteDimensional k (cohomology (relativeDifferentials f) (structureCoeff f) i) := by
  have := hp.isProper
  obtain ⟨P, hP⟩ := exists_isSeparable_chartPair f hp hdim hpt
  exact ⟨finiteDimensional_cohomology_structure P f hnormal htf hP i,
    finiteDimensional_cohomology_kaehler P f hnormal htf hP i⟩

end DeJongAlterations.StableModification.CurvesField.DualityScheme
