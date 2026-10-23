/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.RegularSmooth
import DeJongAlterations.Algebra.RegularSmoothConverseFormalSmooth

/-!
# The geometric regular-to-smooth converse over a perfect field

The actual base stalk is canonically the original perfect field. The native
finite-type stalk map then allows the local algebra theorem to be applied to
the actual scheme local ring, giving membership in the native smooth locus.
-/

open AlgebraicGeometry CategoryTheory

set_option autoImplicit false

namespace DeJongAlterations.Geometry.RegularSmoothConverse

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

/-- The actual field-spectrum stalk, presented with its native coefficient algebra. -/
abbrev specFieldStalk (s : Spec (CommRingCat.of k)) : CommRingCat :=
  (Spec.structureSheaf k).presheaf.stalk s

/-- The canonical algebra equivalence between a field and any actual stalk of its spectrum. -/
def specFieldStalkEquiv (s : Spec (CommRingCat.of k)) :
    k ≃ₐ[k] specFieldStalk s :=
  IsLocalization.atUnits _ s.asIdeal.primeCompl
    (fun a ha ↦ by aesop (add simp IsUnit.mem_submonoid_iff))

/-- The actual local ring of the spectrum of a field is itself a field. -/
theorem specFieldStalk_isField (s : Spec (CommRingCat.of k)) :
    IsField (specFieldStalk s) :=
  (specFieldStalkEquiv s).toRingEquiv.symm.isField (Field.toIsField k)

/-- Perfection passes through the canonical field-to-stalk equivalence. -/
theorem specFieldStalk_perfect [PerfectField k] (s : Spec (CommRingCat.of k)) :
    letI := (specFieldStalk_isField s).toField
    PerfectField (specFieldStalk s) := by
  let := (specFieldStalk_isField s).toField
  have : Algebra.IsAlgebraic k (specFieldStalk s) :=
    .of_injective (specFieldStalkEquiv s).symm.toAlgHom (specFieldStalkEquiv s).symm.injective
  exact Algebra.IsAlgebraic.perfectField (K := k)
    (L := specFieldStalk s)

variable [PerfectField k] {X : Scheme.{u}}

/-- A regular actual scheme stalk makes its actual structural stalk map formally smooth. -/
theorem formallySmooth_stalkMap_of_isRegularLocalRing
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    (p.stalkMap x).hom.FormallySmooth := by
  let B := specFieldStalk (p x)
  let : Field B := (specFieldStalk_isField (p x)).toField
  let : PerfectField B := specFieldStalk_perfect (p x)
  let : Algebra B (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType B (X.presheaf.stalk x) := LocallyOfFiniteType.stalkMap p x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hx
  exact Algebra.RegularSmoothConverseFormalSmooth.formallySmooth_of_isRegularLocalRing
    B (X.presheaf.stalk x)

/-- Every actual regular local ring gives membership in the native smooth locus over a perfect field. -/
theorem mem_smoothLocus_of_isRegularLocalRing
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x)) : x ∈ p.smoothLocus :=
  (Scheme.Hom.mem_smoothLocus).mpr (formallySmooth_stalkMap_of_isRegularLocalRing p x hx)

/-- Actual regular schemes locally of finite type over perfect fields are smooth. -/
theorem smooth_of_isRegularScheme
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (hX : IsRegularScheme X) : Smooth p := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  exact mem_smoothLocus_of_isRegularLocalRing p x (hX x)

/-- The native smooth locus is exactly the actual regular-local-ring locus. -/
theorem mem_smoothLocus_iff_isRegularLocalRing
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    x ∈ p.smoothLocus ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨RegularSmooth.isRegularLocalRing_of_mem_smoothLocus p x,
    mem_smoothLocus_of_isRegularLocalRing p x⟩

/-- The full set equality in de Jong 2.10, using the actual native smooth locus. -/
theorem smoothLocus_eq_regular_set
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    (p.smoothLocus : Set X) = {x | IsRegularLocalRing (X.presheaf.stalk x)} := by
  ext x
  exact mem_smoothLocus_iff_isRegularLocalRing p x

/-- The actual regular-local-ring locus is open over a perfect field. -/
theorem isOpen_regularLocus
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    IsOpen {x : X | IsRegularLocalRing (X.presheaf.stalk x)} := by
  rw [← smoothLocus_eq_regular_set p]
  exact p.smoothLocus.isOpen

/-- Smoothness and actual stalkwise regularity agree over a perfect field. -/
theorem smooth_iff_isRegularScheme
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    Smooth p ↔ IsRegularScheme X := by
  refine ⟨?_, smooth_of_isRegularScheme p⟩
  intro h
  let := h
  exact RegularSmooth.isRegularScheme_of_smooth p

end

end DeJongAlterations.Geometry.RegularSmoothConverse
