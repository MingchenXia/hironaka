/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs

/-!
# The affine blow-ups over the affine opens of a scheme, and their gluing

The blow-up of a scheme `X` along an ideal sheaf `I` is `Proj_X (⨁ₙ Iⁿ)`, obtained by gluing the
affine blow-ups `Proj Rees(I(U))` over the affine opens `U` of `X` along the canonical
isomorphisms `π⁻¹(U) ≅ Proj Rees(I(U))` [Sta, Tags 01OF and 0804]; the relative gluing lemma
[Sta, Tag 01LH] performs this from the functor
`affineBlowUpFunctor I : U ↦ affineBlowUp (I.ideal U)` on the affine opens, the natural
transformation `affineBlowUpNatTrans I` to the directed cover's diagram
`X.directedAffineCover.functorOfLocallyDirected`, and a proof `h` that its naturality squares are
pullbacks; the result is `blowUpOf I h` over `X`. This module supplies the rest of the
construction.

* `affineBlowUpFunctor_obj`, `affineBlowUpFunctor_map`, `affineBlowUpNatTrans_app`: the functor
  and the components `affineBlowUp.π ≫ U.isoSpec.inv : affineBlowUp (I.ideal U) ⟶ U`, unfolded.
* Every naturality square is a pullback (`(affineBlowUpNatTrans I).Equifibered`, the hypothesis
  of the relative gluing lemma; [Hau14, Corollary 5.2 (b)]): `equifibered_of_isPullback I H`
  derives it from the open-restriction square `H` of the universal property of the affine
  blow-up (`affineBlowUp.isPullback_mapHom` of
  `Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Restrict`), pasted with the square of isomorphisms
  `Spec Γ(X, U) ≅ U ⊆ V ≅ Spec Γ(X, V)`.
* For an arbitrary proof `h` of the pullback squares: the components `blowUpOf.ι I h U` of the
  gluing, and Mathlib's pullback squares `blowUpOf.isPullback I h U` —
  `π⁻¹(U) ≅ affineBlowUp (I.ideal U)` over `U` [Sta, Tag 0804].  The blow-up itself,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowUp I`, is `blowUpOf I` at the proof from the
  universal property.
* The side condition `Quiver.IsThin X.affineOpens` of the gluing (a preorder category), supplied
  here as `fun _ _ => inferInstance`.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Polynomial

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Morphisms of the preorder category `X.affineOpens` form a subsingleton (they are
`ULift (PLift (U ≤ V))`); Mathlib has no `Quiver.IsThin` instance for preorder categories. -/
instance : Quiver.IsThin X.affineOpens := fun _ _ => inferInstance

section Functor

@[simp]
theorem affineBlowUpFunctor_obj (U : X.affineOpens) :
    (affineBlowUpFunctor I).obj U = affineBlowUp (I.ideal U) :=
  rfl

theorem affineBlowUpFunctor_map {U V : X.affineOpens} (h : U ⟶ V) :
    (affineBlowUpFunctor I).map h =
      affineBlowUp.mapHom (R := Γ(X, V)) (S := Γ(X, U)) (I := I.ideal V) (J := I.ideal U)
        (X.presheaf.map (homOfLE h.le).op) (I.map_ideal h.le) :=
  rfl

@[simp]
theorem affineBlowUpNatTrans_app (U : X.affineOpens) :
    (affineBlowUpNatTrans I).app U =
      affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv :=
  rfl

end Functor

section Equifibered

variable {I}

/-- For affine opens `U ≤ V`, `Spec` of the restriction `Γ(X, V) → Γ(X, U)` is
`Spec Γ(X, U) ≅ U ⊆ V ≅ Spec Γ(X, V)` (Mathlib's `Scheme.Opens.toSpecΓ_SpecMap_presheaf_map`
read through `IsAffineOpen.isoSpec`). -/
theorem specMap_presheaf_map_isoSpec_inv {U V : X.affineOpens} (hle : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hle).op) ≫
        (affineOpens_isAffineOpen V).isoSpec.inv =
      (affineOpens_isAffineOpen U).isoSpec.inv ≫ X.homOfLE (show (U : X.Opens) ≤ V from hle) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.isoSpec_hom]
  exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ hle

theorem specMap_presheaf_map_eq {U V : X.affineOpens} (hle : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hle).op) =
      ((affineOpens_isAffineOpen U).isoSpec.inv ≫
        X.homOfLE (show (U : X.Opens) ≤ V from hle)) ≫ (affineOpens_isAffineOpen V).isoSpec.hom :=
  (Iso.comp_inv_eq _).mp (specMap_presheaf_map_isoSpec_inv hle)

/-- For affine opens `U ≤ V` of `X`, `Spec Γ(X, U) → Spec Γ(X, V)` is an open immersion (it is
the inclusion `U ⊆ V` up to the isomorphisms `isoSpec`): the hypothesis under which the
open-restriction square `affineBlowUp.isPullback_mapHom` applies to the restriction maps of the
structure sheaf. -/
instance isOpenImmersion_specMap_presheaf_map {U V : X.affineOpens} (hle : U ≤ V) :
    IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hle).op)) := by
  rw [specMap_presheaf_map_eq hle]
  infer_instance

variable (I)

/-- Given the open-restriction square `H` of the universal property for every ring map `φ` with
`Spec.map φ` an open immersion, every naturality square of `affineBlowUpNatTrans I` is a pullback
— the hypothesis of the relative gluing lemma [Sta, Tag 01LH]; [Hau14, Corollary 5.2 (b)].
Proof: the square `H` for the restriction `Γ(X, V) → Γ(X, U)` (an open immersion on `Spec` by
`isOpenImmersion_specMap_presheaf_map`), pasted vertically with the commutative square of
isomorphisms `Spec Γ(X, U) ≅ U`, `Spec Γ(X, V) ≅ V` over `U ⊆ V` (a pullback because its
vertical sides are isomorphisms). -/
theorem equifibered_of_isPullback
    (H : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)] {I : Ideal R}
      {J : Ideal S} (hJ : I.map φ.hom = J),
      IsPullback (affineBlowUp.mapHom φ hJ) (affineBlowUp.π J) (affineBlowUp.π I) (Spec.map φ)) :
    (affineBlowUpNatTrans I).Equifibered := by
  intro U V h
  have hle : U ≤ V := h.le
  have hle' : (U : X.Opens) ≤ V := hle
  obtain rfl : h = homOfLE hle := (homOfLE_leOfHom h).symm
  change IsPullback (affineBlowUp.mapHom (R := Γ(X, V)) (S := Γ(X, U)) (I := I.ideal V)
      (J := I.ideal U) (X.presheaf.map (homOfLE (X := X.Opens) hle).op) (I.map_ideal hle))
    (affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv)
    (affineBlowUp.π (I.ideal V) ≫ (affineOpens_isAffineOpen V).isoSpec.inv) (X.homOfLE hle')
  have hφ := isOpenImmersion_specMap_presheaf_map hle
  exact (@H _ _ _ hφ _ _ (I.map_ideal hle)).paste_vert
    (IsPullback.of_vert_isIso ⟨specMap_presheaf_map_isoSpec_inv hle⟩)

end Equifibered

section Gluing

variable (h : (affineBlowUpNatTrans I).Equifibered)

/-- The component `affineBlowUp (I.ideal U) ⟶ blowUpOf I h` of the gluing, an open immersion. -/
noncomputable def blowUpOf.ι (U : X.affineOpens) : affineBlowUp (I.ideal U) ⟶ blowUpOf I h :=
  Limits.colimit.ι (relativeGluingDataOf I h).functor U

/-- Over the base, the component `ι U` is `affineBlowUp.π` followed by `U ≅ Spec Γ(X, U)` and the
inclusion of `U` [Sta, Tag 01LH]. -/
theorem blowUpOf.ι_π (U : X.affineOpens) :
    blowUpOf.ι I h U ≫ blowUpOf.π I h =
      (affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv) ≫ U.1.ι :=
  (relativeGluingDataOf I h).ι_toBase U

/-- The local description of the blow-up [Sta, Tag 0804]: over each affine open `U`,
`π⁻¹(U) ≅ affineBlowUp (I.ideal U)`, as Mathlib's pullback square `isPullback_natTrans_ι_toBase`. -/
theorem blowUpOf.isPullback (U : X.affineOpens) :
    IsPullback (affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv)
      (blowUpOf.ι I h U) U.1.ι (blowUpOf.π I h) :=
  (relativeGluingDataOf I h).isPullback_natTrans_ι_toBase U

end Gluing

end AlgebraicGeometry
