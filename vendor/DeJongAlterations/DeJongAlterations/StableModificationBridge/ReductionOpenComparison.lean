/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.ReductionCanonicalGeometry
import DeJongAlterations.Geometry.SNCLocality

/-!
# The actual reduction of an original open subscheme

The native nilradical restriction and native pullback isomorphisms identify the reduction
of an actual original open with its actual inverse image under the original reduction map.

Blueprint: `reduction-open-comparison.tex`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace DeJongAlterations.StableModificationBridge.ReductionOpenComparison

noncomputable section

theorem nilradical_comap {X : Scheme.{u}} (U : X.Opens) :
    X.nilradical.comap U.ι = U.toScheme.nilradical := by
  have htop : (⊤ : TopologicalSpace.Closeds X).preimage U.ι.continuous = ⊤ := by
    ext x
    rfl
  simpa only [htop, Scheme.IdealSheafData.vanishingIdeal_top] using
    Geometry.SNCLocality.comap_vanishingIdeal U.ι ⊤

private theorem eqToIso_subscheme_ι {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

def iso {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme.nilradical.subscheme ≅ (X.nilradical.subschemeι ⁻¹ᵁ U).toScheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (nilradical_comap U).symm) ≪≫
    X.nilradical.comapIso U.ι ≪≫ pullbackSymmetry U.ι X.nilradical.subschemeι ≪≫
      pullbackRestrictIsoRestrict X.nilradical.subschemeι U

@[reassoc (attr := simp)]
theorem iso_hom_restrict {X : Scheme.{u}} (U : X.Opens) :
    (iso U).hom ≫ X.nilradical.subschemeι ∣_ U = U.toScheme.nilradical.subschemeι := by
  simp only [iso, Iso.trans_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict,
    pullbackSymmetry_hom_comp_snd, Scheme.IdealSheafData.comapIso_hom_fst]
  exact eqToIso_subscheme_ι _ _ (nilradical_comap U).symm

@[reassoc (attr := simp)]
theorem iso_hom_structure {X : Scheme.{u}} (U : X.Opens) :
    (iso U).hom ≫ (X.nilradical.subschemeι ⁻¹ᵁ U).ι ≫ X.nilradical.subschemeι =
      U.toScheme.nilradical.subschemeι ≫ U.ι := by
  rw [← morphismRestrict_ι, iso_hom_restrict_assoc]

theorem isAffine_reduction_of_preimage {X : Scheme.{u}} (U : X.Opens)
    (h : IsAffineOpen (X.nilradical.subschemeι ⁻¹ᵁ U)) :
    IsAffine U.toScheme.nilradical.subscheme := by
  let : IsAffine (X.nilradical.subschemeι ⁻¹ᵁ U).toScheme := h
  exact (IsAffine.iff_of_isIso (iso U).hom).mpr inferInstance

def liftOpen {X : Scheme.{u}} (W : X.nilradical.subscheme.Opens) : X.Opens :=
  ⟨ReductionCanonicalGeometry.homeomorph X '' W,
    (ReductionCanonicalGeometry.homeomorph X).isOpenMap _ W.isOpen⟩

@[simp]
theorem preimage_liftOpen {X : Scheme.{u}} (W : X.nilradical.subscheme.Opens) :
    X.nilradical.subschemeι ⁻¹ᵁ liftOpen W = W := by
  apply TopologicalSpace.Opens.ext
  exact (ReductionCanonicalGeometry.homeomorph X).preimage_image W

end

end DeJongAlterations.StableModificationBridge.ReductionOpenComparison
