/-
Copyright (c) 2026. All rights reserved.

The affine adjunction proof `comap_ideal_top_of_isAffine` below is reused from
EnvelopeProperty/EnvelopeProperty/Berkovich/SchemeIdealPullback.lean, lines 26–43.
Source SHA256: 3c49329323300527b44dcf140b52f0f090b052d7c7595382e91eed7f0e161879.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Native ideal sheaves on affine spectra and actual pullback

The affine ideal-sheaf equivalence is combined with the canonical global-coordinate
isomorphism. Geometric pullback along the actual spectrum map is proved to correspond
exactly to extension of ideals, by the genuine pullback--pushforward adjunction.
-/

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

noncomputable section

namespace DeJongAlterations.Geometry.SpecIdealSheaf

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- The actual scheme ideal pullback has the genuine section-ring image on affine schemes. -/
theorem comap_ideal_top_of_isAffine [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  let K := (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom
  let J : X.IdealSheafData := ofIdealTop K
  have hJ : I ≤ J.map f := by
    apply le_of_isAffine
    rw [ideal_map_of_isAffineHom]
    simpa [J, ofIdealTop_ideal, Scheme.Hom.appTop] using
      (Ideal.le_comap_map : I.ideal ⟨⊤, isAffineOpen_top Y⟩ ≤ K.comap f.appTop.hom)
  have hleft := ((le_map_iff_comap_le (I := J) (J := I) (f := f)).mp hJ) ⟨⊤, isAffineOpen_top X⟩
  have hright := (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩
  rw [ideal_map_of_isAffineHom] at hright
  apply le_antisymm
  · simpa [J, ofIdealTop_ideal] using hleft
  · exact Ideal.map_le_iff_le_comap.mpr hright

variable (R : Type u) [CommRing R]

/-- Native ideal sheaves on `Spec R`, identified with ideals of its actual coordinate ring. -/
def specIdealSheafEquiv : (Spec (CommRingCat.of R)).IdealSheafData ≃o Ideal R :=
  (Scheme.IdealSheafData.equivOfIsAffine (X := Spec (CommRingCat.of R))).toOrderIso.trans
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.idealComapOrderIso

/-- The actual native ideal sheaf associated with the specified coordinate ideal. -/
def specIdealSheaf (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  (specIdealSheafEquiv R).symm I

/-- The coordinate ideal is contraction of the actual global ideal under the coordinate isomorphism. -/
theorem specIdealSheafEquiv_apply (J : (Spec (CommRingCat.of R)).IdealSheafData) :
    specIdealSheafEquiv R J =
      (J.ideal ⟨⊤, isAffineOpen_top _⟩).comap
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl

/-- The global ideal of the associated native sheaf is exactly extension along the coordinate iso. -/
theorem specIdealSheaf_ideal_top (I : Ideal R) :
    (specIdealSheaf R I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  change (ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).ideal _ = _
  simp

/-- Taking the actual coordinate ideal recovers the original ring ideal. -/
@[simp]
theorem specIdealSheafEquiv_specIdealSheaf (I : Ideal R) :
    specIdealSheafEquiv R (specIdealSheaf R I) = I :=
  (specIdealSheafEquiv R).apply_symm_apply I

/-- Every native ideal sheaf on a spectrum is recovered from its actual coordinate ideal. -/
@[simp]
theorem specIdealSheaf_specIdealSheafEquiv
    (J : (Spec (CommRingCat.of R)).IdealSheafData) :
    specIdealSheaf R (specIdealSheafEquiv R J) = J :=
  (specIdealSheafEquiv R).symm_apply_apply J

variable {R} {S : Type u} [CommRing S]

/-- The actual geometric pullback along `Spec.map f` is extension of the original coordinate ideal. -/
theorem specIdealSheaf_comap (f : R →+* S) (I : Ideal R) :
    (specIdealSheaf R I).comap (Spec.map (CommRingCat.ofHom f)) =
      specIdealSheaf S (I.map f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_ideal_top_of_isAffine, specIdealSheaf_ideal_top, specIdealSheaf_ideal_top,
    Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

/-- Pullback of any native affine ideal sheaf has the genuine coordinate image under `f`. -/
theorem specIdealSheafEquiv_comap (f : R →+* S)
    (J : (Spec (CommRingCat.of R)).IdealSheafData) :
    specIdealSheafEquiv S (J.comap (Spec.map (CommRingCat.ofHom f))) =
      (specIdealSheafEquiv R J).map f := by
  have H := specIdealSheaf_comap f (specIdealSheafEquiv R J)
  rw [specIdealSheaf_specIdealSheafEquiv] at H
  simpa only [specIdealSheafEquiv_specIdealSheaf] using congrArg (specIdealSheafEquiv S) H

end DeJongAlterations.Geometry.SpecIdealSheaf
