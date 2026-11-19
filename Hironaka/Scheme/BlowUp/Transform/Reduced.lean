/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Hironaka.Scheme.BlowUp.AffineBlowUpAlgebra
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Glue.GlobalCharts
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# Blow-ups of reduced schemes are reduced; the strict transform of a reduced subscheme is reduced

The chart rings `Γ(X, U)[I(U)/a]` of the blow-up are subalgebras of the localizations
`Γ(X, U)_a` (`affineBlowUpAlgebra`), hence reduced when `X` is; the charts cover `blowUp I`, so
`blowUp I` is reduced [Sta, Tag 0808]. The strict transform of a closed subscheme `V(J)` is the
blow-up of `V(J)` along the restricted centre [Sta, Tag 080E], hence reduced when `V(J)` is.
These are used for the generic points of the strict transforms in the resolution of a reduced
scheme, where the strict transform of a component is again integral [Kol07, Corollary 22, proof].

## Conventions

`D.blowUp` and `D.blowUpπ` are the blow-up along `D` and its projection, `D.exceptionalDivisor` is
`D.comap D.blowUpπ`, and `J.strictTransform D` is
`strictTransformAlong (D.blowUpπ) (D.exceptionalDivisor) J`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/-! ### Reduced chart rings -/

section ChartRing

variable {R : Type u} [CommRing R]

/-- The chart ring `R[I/a]` is a subalgebra of `R_a` (`affineBlowUpAlgebra`), hence reduced when
`R` is (localizations of reduced rings are reduced). -/
instance isReduced_affineBlowUpAlgebra [_root_.IsReduced R] (I : Ideal R) (a : R) :
    _root_.IsReduced (affineBlowUpAlgebra I a) :=
  isReduced_of_injective (affineBlowUpAlgebra I a).val Subtype.val_injective

end ChartRing

/-! ### The blow-up of a reduced scheme is reduced -/

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The blow-up of a reduced scheme is reduced [Sta, Tag 0808] — every point lies in a chart
`Spec Γ(X, U)[I(U)/a]` (`blowUp.iUnion_range_chart`), an open immersion, and the chart ring is
reduced. -/
theorem Scheme.IdealSheafData.blowUp.isReduced [IsReduced X] : IsReduced (blowUp I) := by
  have h : ∀ y : blowUp I, _root_.IsReduced ((blowUp I).presheaf.stalk y) := fun y => by
    obtain ⟨U, hU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem (blowUpπ I y)
    have hy : y ∈ ⋃ a : I.ideal U, Set.range (blowUp.chart I U a) := by
      rw [blowUp.iUnion_range_chart]
      exact hU
    obtain ⟨a, x, rfl⟩ := Set.mem_iUnion.mp hy
    have : _root_.IsReduced Γ(X, U) := (inferInstance : IsReduced X).component_reduced U
    have : IsReduced (Spec (.of (affineBlowUpAlgebra (I.ideal U) a))) := inferInstance
    exact isReduced_of_injective _
      (asIso ((blowUp.chart I U a).stalkMap x)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/-! ### The strict transform of a reduced closed subscheme is reduced -/

/-- The strict transform `V(Jˢ) ⊆ blowUp D` of a reduced closed subscheme `V(J)` is isomorphic to
the blow-up of `V(J)` along the restricted centre (`exists_iso_strictTransform_subscheme`)
[Sta, Tag 080E], which is reduced. -/
theorem isReduced_strictTransformAlong_subscheme (D J : X.IdealSheafData)
    [IsReduced J.subscheme] :
    IsReduced (J.strictTransformAlong (blowUpπ D) (D.comap (blowUpπ D))).subscheme := by
  obtain ⟨e, -⟩ := exists_iso_strictTransform_subscheme (blowUp.isBlowUp D)
    (blowUp.isBlowUp (D.comap J.subschemeι))
  have : IsReduced (blowUp (D.comap J.subschemeι)) := blowUp.isReduced _
  exact isReduced_of_isOpenImmersion e.inv

/-- The strict transform `J.strictTransform D` of the
vocabulary of the main theorems, of a reduced closed subscheme, is reduced. -/
theorem isReduced_strictTransform_subscheme (D J : X.IdealSheafData) [IsReduced J.subscheme] :
    IsReduced (J.strictTransform D).subscheme :=
  isReduced_strictTransformAlong_subscheme D J

end AlgebraicGeometry
