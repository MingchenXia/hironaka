/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.AffineBlowupFunctor
import DeJongAlterations.Geometry.AffineBlowupBaseChange
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The global native blowup of an ideal sheaf

The actual affine Rees projective spectra form an equifibered diagram over the native
small affine Zariski site. Relative gluing constructs their global scheme and structure map.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace DeJongAlterations.Geometry.BlowupGluing

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The actual coefficient restriction associated to an arrow of the affine Zariski site. -/
def coefficientMap {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    Γ(X, V.1) →+* Γ(X, U.1) :=
  (X.presheaf.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).op).hom

/-- The native centre ideals agree under the actual restriction homomorphism. -/
theorem center_map {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (D.ideal ⟨V.1, V.2⟩).map (coefficientMap h) = D.ideal ⟨U.1, U.2⟩ :=
  D.map_ideal ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).le

/-- The actual coefficient restrictions preserve identities. -/
@[simp]
theorem coefficientMap_id (U : X.AffineZariskiSite) :
    coefficientMap (𝟙 U) = RingHom.id Γ(X, U.1) := by
  simp [coefficientMap]
  rfl

/-- The actual coefficient restrictions compose contravariantly. -/
@[simp]
theorem coefficientMap_comp {U V W : X.AffineZariskiSite} (h : U ⟶ V) (k : V ⟶ W) :
    coefficientMap (h ≫ k) = (coefficientMap h).comp (coefficientMap k) := by
  simp [coefficientMap]

/-- Every actual coefficient map of the small affine site is an ordinary principal localization. -/
theorem coefficientMap_isLocalization {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    ∃ s : Γ(X, V.1), letI := (coefficientMap h).toAlgebra
      IsLocalization.Away s Γ(X, U.1) := by
  obtain ⟨s, hs⟩ := h.le
  refine ⟨s, ?_⟩
  have hU : U = V.basicOpen s := Subtype.ext hs.symm
  subst U
  have hh : h = homOfLE (V.basicOpen_le s) := Subsingleton.elim _ _
  subst h
  exact V.2.isLocalization_basicOpen s

private theorem affineBlowupMapTo_congr_coeff {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) {f g : R →+* S}
    (hf : I.map f = J) (hg : I.map g = J) (hfg : f = g) :
    affineBlowupMapTo I J f hf = affineBlowupMapTo I J g hg := by
  cases hfg
  rfl

/-- The actual affine blowup diagram, with the centre ideal at each affine open fixed by D. -/
def affineDiagram : X.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := affineBlowup (D.ideal ⟨U.1, U.2⟩)
  map {U V} h := affineBlowupMapTo (D.ideal ⟨V.1, V.2⟩) (D.ideal ⟨U.1, U.2⟩)
    (coefficientMap h) (center_map D h)
  map_id U := by
    exact (affineBlowupMapTo_congr_coeff _ _ (center_map D (𝟙 U))
      (by simp) (coefficientMap_id U)).trans (affineBlowupMapTo_id _ (by simp))
  map_comp {U V W} h k := by
    have hIL : (D.ideal ⟨W.1, W.2⟩).map ((coefficientMap h).comp (coefficientMap k)) =
        D.ideal ⟨U.1, U.2⟩ := by
      rw [← Ideal.map_map, center_map D k, center_map D h]
    exact (affineBlowupMapTo_congr_coeff _ _ (center_map D (h ≫ k)) hIL
      (coefficientMap_comp h k)).trans (affineBlowupMapTo_comp (D.ideal ⟨W.1, W.2⟩) (D.ideal ⟨V.1, V.2⟩)
      (D.ideal ⟨U.1, U.2⟩) (coefficientMap k) (coefficientMap h)
      (center_map D k) (center_map D h) hIL).symm

/-- The actual affine structure maps, before the canonical identification of affine opens
with spectra of their section rings. -/
def structureNatTrans : affineDiagram D ⟶
    Scheme.AffineZariskiSite.toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec where
  app U := affineBlowupStructure (D.ideal ⟨U.1, U.2⟩)
  naturality {U V} h := by
    exact affineBlowupMapTo_structure (D.ideal ⟨V.1, V.2⟩) (D.ideal ⟨U.1, U.2⟩)
      (coefficientMap h) (center_map D h)

/-- The actual affine blowup diagram is equifibered, using the true localization property
of every native affine-site restriction. -/
theorem structureNatTrans_equifibered : (structureNatTrans D).Equifibered := by
  intro U V h
  obtain ⟨s, hs⟩ := coefficientMap_isLocalization h
  let := (coefficientMap h).toAlgebra
  have : IsLocalization.Away s Γ(X, U.1) := hs
  exact AffineBlowupBaseChange.isPullback_affineBlowupMapTo_of_isLocalization
    (D.ideal ⟨V.1, V.2⟩) (D.ideal ⟨U.1, U.2⟩) s (center_map D h)

/-- Genuine relative gluing data, constructed from the actual ideal sheaf alone. -/
def relativeGluingData : (Scheme.AffineZariskiSite.directedCover X).RelativeGluingData where
  functor := affineDiagram D
  natTrans := structureNatTrans D ≫ (Scheme.AffineZariskiSite.restrictIsoSpec X).inv
  equifibered := (structureNatTrans_equifibered D).comp (.of_isIso _)

/-- The global native blowup, obtained by gluing its actual affine Rees projective spectra. -/
def blowup : Scheme.{u} := (relativeGluingData D).glued

/-- The actual global blowup structure morphism to the original scheme. -/
def blowupStructure : blowup D ⟶ X := (relativeGluingData D).toBase

/-- The canonical open cover by the actual affine blowups on the native affine site. -/
abbrev blowupCover : (blowup D).OpenCover := (relativeGluingData D).cover

/-- The canonical inclusion of an actual affine Rees blowup into the glued scheme. -/
def chartInclusion (U : X.AffineZariskiSite) :
    affineBlowup (D.ideal ⟨U.1, U.2⟩) ⟶ blowup D := (blowupCover D).f U

/-- The global open cover has exactly the prescribed native affine blowup objects. -/
@[simp]
theorem blowupCover_X (U : X.AffineZariskiSite) :
    (blowupCover D).X U = affineBlowup (D.ideal ⟨U.1, U.2⟩) := rfl

/-- The global open-cover maps are precisely the canonical native chart inclusions. -/
@[simp]
theorem blowupCover_f (U : X.AffineZariskiSite) :
    (blowupCover D).f U = chartInclusion D U := rfl

instance chartInclusion_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (chartInclusion D U) :=
  inferInstanceAs (IsOpenImmersion ((blowupCover D).f U))

/-- Each actual affine chart inclusion has the prescribed global structure-map triangle. -/
@[reassoc]
theorem chartInclusion_structure (U : X.AffineZariskiSite) :
    chartInclusion D U ≫ blowupStructure D =
      affineBlowupStructure (D.ideal ⟨U.1, U.2⟩) ≫ U.2.fromSpec := by
  have h := (relativeGluingData D).ι_toBase U
  change chartInclusion D U ≫ blowupStructure D =
    (affineBlowupStructure (D.ideal ⟨U.1, U.2⟩) ≫ U.2.isoSpec.inv) ≫ U.1.ι at h
  exact h.trans (by rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι])

/-- The native affine blowup is the exact pullback over the corresponding actual base open. -/
theorem isPullback_chartOpen (U : X.AffineZariskiSite) :
    IsPullback (affineBlowupStructure (D.ideal ⟨U.1, U.2⟩) ≫ U.2.isoSpec.inv)
      (chartInclusion D U) U.1.ι (blowupStructure D) :=
  (relativeGluingData D).isPullback_natTrans_ι_toBase U

/-- The native affine blowup is the exact pullback over the actual spectrum chart of X. -/
theorem isPullback_chart (U : X.AffineZariskiSite) :
    IsPullback (affineBlowupStructure (D.ideal ⟨U.1, U.2⟩))
      (chartInclusion D U) U.2.fromSpec (blowupStructure D) := by
  refine (isPullback_chartOpen D U).of_iso (Iso.refl _) U.2.isoSpec
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using U.2.isoSpec_hom_fromSpec.symm
  · simp

/-- The global affine chart image is exactly the inverse image of its original affine open. -/
theorem chartInclusion_opensRange (U : X.AffineZariskiSite) :
    (chartInclusion D U).opensRange = blowupStructure D ⁻¹ᵁ U.1 := by
  have h := (relativeGluingData D).toBase_preimage_eq_opensRange_ι U
  change blowupStructure D ⁻¹ᵁ U.1.ι.opensRange = (chartInclusion D U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h.symm

end

end DeJongAlterations.Geometry.BlowupGluing
