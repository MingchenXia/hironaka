/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModification.CurvesField.AmplePositiveIntegral
import DeJongAlterations.Geometry.LineBundleIsoEuler

/-! # Weak Riemann--Roch for the original line-bundle powers and field coefficients -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.CurveLineBundle

universe u

open StableModification StableModification.Projectivity StableModification.Cohomology
open CurvesField CurvesField.Positive

set_option backward.isDefEq.respectTransparency false

/-- Internally produce every original two-chart, regularity and finite-quotient
input for the same original Euler-characteristic power formula. -/
theorem eulerCharOf_twist_eq {K : Type u} [Field K] [Infinite K]
    {X : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundleData X) (n : ℕ) :
    DualityScheme.eulerCharOf (L.twist (unitModule X) n) (structureCoeff p) =
      DualityScheme.eulerCharOf (unitModule X) (structureCoeff p) +
        n * Positive.degree L (structureCoeff p) := by
  let : IsProper p := hp.isProper
  obtain ⟨P, hηU, hηV⟩ := exists_presentation_of_isIntegral hp hdim L
  obtain ⟨a, j, ha⟩ := P.exists_numerator
  let c := structureCoeff p
  have : FiniteDimensional K (cohomology (unitModule X) c 0) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X) (fun W _ => Module.Finite.self _) 0
  have : FiniteDimensional K (cohomology (unitModule X) c 1) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X) (fun W _ => Module.Finite.self _) 1
  have hUV : ((P.U ⊓ P.V : X.Opens) : Set X).Nonempty := ⟨genericPoint X, hηU, hηV⟩
  have : Nonempty P.V := ⟨⟨genericPoint X, hηV⟩⟩
  have ha0 : a ≠ 0 := ne_zero_of_isUnit_res inf_le_right hUV (P.isUnit_resV_of_numerator ha)
  have hf0 : P.f ≠ 0 := ne_zero_of_isUnit_res inf_le_right hUV P.isUnit_resV_f
  have := finiteDimensional_quotient_fMul (p := p) hdim P.isAffineOpen_V ha0
  have := finiteDimensional_quotient_fMul (p := p) hdim P.isAffineOpen_V hf0
  exact P.eulerCharOf_twist_eq c ha (injective_fMul_of_ne_zero ha0)
    (injective_fMul_of_ne_zero hf0) n

end DeJongAlterations.Geometry.CurveLineBundle
