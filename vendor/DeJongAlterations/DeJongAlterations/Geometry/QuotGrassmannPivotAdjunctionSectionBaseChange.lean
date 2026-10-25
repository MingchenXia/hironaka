import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Reusable adjunction-mate section base change and its exact unit square

This is a generic categorical theorem about the original adjunctions and their
original right-adjoint isomorphism. It introduces no geometric output witness.
Separating the generic proof avoids expanding actual scheme/sheaf adjunction
implementations repeatedly in the kernel.
-/

noncomputable section

open CategoryTheory

namespace DeJongAlterations.Geometry.QuotGrassmann

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {LR : C ⥤ D} {ΓR : D ⥤ C} {P : D ⥤ E} {U : E ⥤ D}
  {L : C ⥤ F} {V : F ⥤ C} {LS : F ⥤ E} {ΓS : E ⥤ F}
  (ar : LR ⊣ ΓR) (ap : P ⊣ U) (ae : L ⊣ V) (asB : LS ⊣ ΓS)
  (β : U ⋙ ΓR ≅ ΓS ⋙ V)

/-- The exact whole left-adjoint mate of the original right-adjoint comparison. -/
def originalAdjunctionSectionBaseChangeIso : LR ⋙ P ≅ L ⋙ LS :=
  ((conjugateIsoEquiv (ar.comp ap) (ae.comp asB)).symm β).symm

/-- The original units, actual mate and original counit give a whole natural section transformation. -/
def originalAdjunctionSectionBaseChange : ΓR ⋙ L ⟶ P ⋙ ΓS :=
  Functor.whiskerLeft (ΓR ⋙ L) asB.unit ≫
    (Functor.isoWhiskerLeft ΓR
      (Functor.isoWhiskerRight (originalAdjunctionSectionBaseChangeIso ar ap ae asB β).symm ΓS)).hom ≫
    Functor.whiskerRight ar.counit (P ⋙ ΓS)

/-- The WHOLE section transformation preserves the ORIGINAL adjunction units for EVERY original object. -/
theorem originalAdjunctionSectionBaseChange_unit (M : D) :
    ae.unit.app (ΓR.obj M) ≫
      V.map ((originalAdjunctionSectionBaseChange ar ap ae asB β).app M) =
    ΓR.map (ap.unit.app M) ≫ β.hom.app (P.obj M) := by
  let α := originalAdjunctionSectionBaseChangeIso ar ap ae asB β
  let q := P.map (ar.counit.app M)
  have hβ : α.inv = (conjugateEquiv (ar.comp ap) (ae.comp asB)).symm β.hom := rfl
  have hMate : ae.unit.app (ΓR.obj M) ≫ V.map
      (asB.unit.app (L.obj (ΓR.obj M)) ≫ ΓS.map (α.inv.app (ΓR.obj M))) =
      (ar.comp ap).unit.app (ΓR.obj M) ≫ β.hom.app ((LR ⋙ P).obj (ΓR.obj M)) := by
    rw [hβ, V.map_comp]
    have h := (unit_conjugateEquiv_symm (ar.comp ap) (ae.comp asB) β.hom (ΓR.obj M)).symm
    rw [Adjunction.comp_unit_app] at h
    simp only [Functor.comp_map, Category.assoc] at h ⊢
    exact h

  have hr : β.hom.app ((LR ⋙ P).obj (ΓR.obj M)) ≫ V.map (ΓS.map q) =
      ΓR.map (U.map q) ≫ β.hom.app (P.obj M) := (β.hom.naturality q).symm
  have hReduce : (ar.comp ap).unit.app (ΓR.obj M) ≫ ΓR.map (U.map q) =
      ΓR.map (ap.unit.app M) := by
    rw [Adjunction.comp_unit_app, Category.assoc, ← ΓR.map_comp]
    have hn : ap.unit.app (LR.obj (ΓR.obj M)) ≫ U.map q =
        ar.counit.app M ≫ ap.unit.app M := (ap.unit.naturality (ar.counit.app M)).symm
    rw [hn, ΓR.map_comp, ← Category.assoc, ar.right_triangle_components M]
    exact Category.id_comp _
  have hT : (originalAdjunctionSectionBaseChange ar ap ae asB β).app M =
      (asB.unit.app (L.obj (ΓR.obj M)) ≫ ΓS.map (α.inv.app (ΓR.obj M))) ≫ ΓS.map q :=
    (Category.assoc (asB.unit.app (L.obj (ΓR.obj M)))
      (ΓS.map (α.inv.app (ΓR.obj M))) (ΓS.map q)).symm
  calc
    _ = (ae.unit.app (ΓR.obj M) ≫ V.map
        (asB.unit.app (L.obj (ΓR.obj M)) ≫ ΓS.map (α.inv.app (ΓR.obj M)))) ≫
          V.map (ΓS.map q) := by
      rw [hT, V.map_comp, Category.assoc]
    _ = ((ar.comp ap).unit.app (ΓR.obj M) ≫
        β.hom.app ((LR ⋙ P).obj (ΓR.obj M))) ≫ V.map (ΓS.map q) :=
      congrArg (fun a => a ≫ V.map (ΓS.map q)) hMate
    _ = ((ar.comp ap).unit.app (ΓR.obj M) ≫ ΓR.map (U.map q)) ≫ β.hom.app (P.obj M) := by
      simp only [Category.assoc]
      rw [hr]
    _ = _ := congrArg (fun a => a ≫ β.hom.app (P.obj M)) hReduce

end DeJongAlterations.Geometry.QuotGrassmann
