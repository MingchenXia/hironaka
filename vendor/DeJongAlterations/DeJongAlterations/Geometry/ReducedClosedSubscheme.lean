import DeJongAlterations.Geometry.SpecIdealSheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The actual reduced induced closed subscheme

Radical ideal sheaves define reduced native closed subschemes by their genuine affine
quotient cover. Every closed subset therefore has its actual reduced induced structure.
For affine spectra we also compute the support and radical in the original ring coordinates.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData
open DeJongAlterations.Geometry.SpecIdealSheaf

noncomputable section

namespace DeJongAlterations.Geometry.ReducedClosedSubscheme

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

/-- The actual closed subscheme cut out by the radical of any ideal sheaf is reduced. -/
theorem isReduced_radical_subscheme (D : X.IdealSheafData) :
    IsReduced D.radical.subscheme := by
  let : ∀ U, IsReduced (D.radical.subschemeCover.openCover.X U) := by
    intro U
    let : _root_.IsReduced (Γ(X, U.1) ⧸ (D.ideal U).radical) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    exact inferInstanceAs (IsReduced (Spec (CommRingCat.of
      (Γ(X, U.1) ⧸ (D.ideal U).radical))))
  exact IsReduced.of_openCover D.radical.subscheme D.radical.subschemeCover.openCover

/-- The native vanishing ideal sheaf has exactly the prescribed closed support. -/
theorem support_vanishingIdeal (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

/-- The actual vanishing ideal sheaf is radical, without a reducedness certificate. -/
theorem radical_vanishingIdeal (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).radical =
      Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]

/-- The native closed subscheme attached to the vanishing ideal is reduced. -/
theorem isReduced_vanishingIdeal_subscheme (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have H := isReduced_radical_subscheme (Scheme.IdealSheafData.vanishingIdeal Z)
  simpa only [radical_vanishingIdeal] using H

/-- Every closed subset has an actual reduced induced closed subscheme with that exact support. -/
theorem exists_reduced_closed_ideal (Z : Closeds X) :
    ∃ D : X.IdealSheafData, IsReduced D.subscheme ∧ D.support = Z :=
  ⟨Scheme.IdealSheafData.vanishingIdeal Z,
    isReduced_vanishingIdeal_subscheme Z, support_vanishingIdeal Z⟩

variable (R : Type u) [CommRing R]

/-- The associated native ideal sheaf has the zero locus of the original coordinate ideal. -/
theorem specIdealSheaf_support (I : Ideal R) :
    ((specIdealSheaf R I).support : Set (Spec (CommRingCat.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  change (Spec (CommRingCat.of R)).zeroLocus (U := ⊤)
      ((I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :
        Set Γ(Spec (CommRingCat.of R), ⊤)) = _
  rw [Spec_zeroLocus, ← Ideal.coe_comap]
  have H := specIdealSheafEquiv_specIdealSheaf R I
  rw [specIdealSheafEquiv_apply, specIdealSheaf_ideal_top] at H
  exact congrArg (fun J : Ideal R => PrimeSpectrum.zeroLocus (J : Set R)) H

/-- The actual affine ideal-sheaf correspondence commutes with radical. -/
theorem specIdealSheaf_radical (I : Ideal R) :
    (specIdealSheaf R I).radical = specIdealSheaf R I.radical := by
  apply (specIdealSheafEquiv R).injective
  rw [specIdealSheafEquiv_specIdealSheaf, specIdealSheafEquiv_apply]
  change ((specIdealSheaf R I).ideal ⟨⊤, isAffineOpen_top _⟩).radical.comap
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = I.radical
  rw [Ideal.comap_radical]
  exact congrArg Ideal.radical (specIdealSheafEquiv_specIdealSheaf R I)

end DeJongAlterations.Geometry.ReducedClosedSubscheme
