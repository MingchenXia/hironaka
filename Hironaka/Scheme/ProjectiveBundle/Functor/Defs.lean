/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Modules.Defs
public import Hironaka.Scheme.ProjectiveBundle.Affine.Defs
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Hironaka.Scheme.Modules.Sections
public import Hironaka.Scheme.ProjectiveBundle.Affine.Map

/-!
# The projective bundles over the affine opens

For a quasi-coherent sheaf of modules `F` on a scheme `X`, the projective bundle
`P(F) = Proj_X (Sym F)` [Sta, Tag 01OB] is glued from the projective bundles
`P(Γ(F, U)) = Proj (Sym_{Γ(X, U)} Γ(F, U))` of the modules of sections over the affine opens `U`
of `X`, as the blow-up is glued from the affine blow-ups:

* `AlgebraicGeometry.projectiveBundleFunctor F : U ↦ affineProjectiveBundle Γ(X, U) Γ(F, U)`, with
  transition map for `U ≤ V` the morphism `P(Γ(F, U)) ⟶ P(Γ(F, V))` induced by the restriction
  `Γ(F, V) → Γ(F, U)` (`Scheme.Modules.restrictionMap`), semilinear along `Γ(X, V) → Γ(X, U)`;
  its image spans `Γ(F, U)` by quasi-coherence (`Scheme.Modules.span_range_restrictionMap_eq_top`),
  the hypothesis of `Proj.map`;
* `AlgebraicGeometry.projectiveBundleNatTrans F`: the structure morphisms
  `P(Γ(F, U)) ⟶ Spec Γ(X, U) ≅ U`, natural in `U`, to the diagram of the directed cover of `X` by
  its affine opens.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- **The functor of projective bundles** on the affine opens of `X`,
`U ↦ P(Γ(F, U)) = Proj (Sym_{Γ(X, U)} Γ(F, U))`, with transition map for `U ≤ V` the morphism
induced by the restriction `Γ(F, V) → Γ(F, U)` [Sta, Tags 01OB and 01LH]. -/
noncomputable def projectiveBundleFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := affineProjectiveBundle Γ(X, U) Γ(F, U)
  map {U V} h :=
    affineProjectiveBundle.mapHom (R := Γ(X, V)) (S := Γ(X, U)) (X.presheaf.map (homOfLE h.le).op)
      (F.restrictionMap h.le)
      (Scheme.Modules.span_range_restrictionMap_eq_top F (affineOpens_isAffineOpen U)
        (affineOpens_isAffineOpen V) h.le)
  map_id U := by
    have hφ : X.presheaf.map (homOfLE (X := X.Opens) (leOfHom (𝟙 U))).op = 𝟙 Γ(X, U) := by
      rw [show homOfLE (X := X.Opens) (leOfHom (𝟙 U)) = 𝟙 (U : X.Opens) from rfl, op_id,
        CategoryTheory.Functor.map_id]
    refine affineProjectiveBundle.mapHom_eq_id hφ _ (fun x => ?_) _
    change F.presheaf.map (homOfLE (X := X.Opens) (leOfHom (𝟙 U))).op x = x
    rw [show homOfLE (X := X.Opens) (leOfHom (𝟙 U)) = 𝟙 (U : X.Opens) from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  map_comp {U V W} f g := by
    have hχ : X.presheaf.map (homOfLE (X := X.Opens) (leOfHom (f ≫ g))).op =
        X.presheaf.map (homOfLE (X := X.Opens) (leOfHom g)).op ≫
          X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp]
      rfl
    refine affineProjectiveBundle.mapHom_eq_comp hχ _ _ _ (fun x => ?_) _ _ _
    change F.presheaf.map (homOfLE (X := X.Opens) (leOfHom (f ≫ g))).op x =
      F.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op
        (F.presheaf.map (homOfLE (X := X.Opens) (leOfHom g)).op x)
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp]
    rfl

/-- **The structure morphisms** `P(Γ(F, U)) ⟶ Spec Γ(X, U) ≅ U`, as a natural transformation to
the directed affine cover's diagram [Sta, Tag 01LH]. -/
noncomputable def projectiveBundleNatTrans :
    projectiveBundleFunctor F ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app U := affineProjectiveBundle.π Γ(X, U) Γ(F, U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv
  naturality {U V} h := by
    have hle : U ≤ V := h.le
    have hle' : (U : X.Opens) ≤ V := hle
    obtain rfl : h = homOfLE hle := (homOfLE_leOfHom h).symm
    have key : Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hle).op) ≫
        (affineOpens_isAffineOpen V).isoSpec.inv =
        (affineOpens_isAffineOpen U).isoSpec.inv ≫ X.homOfLE hle' := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, IsAffineOpen.isoSpec_hom,
        IsAffineOpen.isoSpec_hom]
      exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ hle'
    change affineProjectiveBundle.mapHom (R := Γ(X, V)) (S := Γ(X, U))
        (X.presheaf.map (homOfLE (X := X.Opens) hle).op) (F.restrictionMap hle)
        (Scheme.Modules.span_range_restrictionMap_eq_top F (affineOpens_isAffineOpen U)
          (affineOpens_isAffineOpen V) hle) ≫
        (affineProjectiveBundle.π Γ(X, V) Γ(F, V) ≫ (affineOpens_isAffineOpen V).isoSpec.inv) =
      (affineProjectiveBundle.π Γ(X, U) Γ(F, U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv) ≫
        X.homOfLE hle'
    rw [affineProjectiveBundle.mapHom_π_assoc, key, Category.assoc]

end AlgebraicGeometry
