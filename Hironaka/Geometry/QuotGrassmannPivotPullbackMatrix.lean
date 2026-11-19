import Hironaka.Geometry.QuotGrassmannPivotPullbackCoefficients

/-!
# Original coordinate projections through true native free-sheaf pullback

The projections are constructed from the actual original free coproduct.
Their native pullbacks are compared using the actual original free frames.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual projection onto an original free coordinate, constructed by its native coproduct. -/
def originalFreeProjection (X : Scheme.{u}) {I : Type u} [DecidableEq I] (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I).desc
    (Cofan.mk (SheafOfModules.unit X.ringCatSheaf) (fun j ↦ if j = i then 𝟙 _ else 0))

/-- Each original projection has its exact original Kronecker coefficient on the original basis. -/
theorem originalFreeProjection_inclusion (X : Scheme.{u}) {I : Type u} [DecidableEq I] (i j : I) :
    SheafOfModules.ιFree j ≫ originalFreeProjection X i = if j = i then 𝟙 _ else 0 :=
  (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I).fac _ (Discrete.mk j)

/-- The actual true pullback of each original projection retains its original coordinate. -/
theorem originalPullbackFreeProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} [DecidableEq I] (i : I) :
    (Scheme.Modules.pullback f).map (originalFreeProjection Y i) ≫
      (originalPullbackUnitIso f).hom =
    (originalPullbackFreeIso f I).hom ≫ originalFreeProjection X i := by
  let F := Scheme.Modules.pullback f
  apply (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan (R := Y.ringCatSheaf) I)).hom_ext
  intro j
  change F.map (SheafOfModules.ιFree j.as) ≫
      (F.map (originalFreeProjection Y i) ≫ (originalPullbackUnitIso f).hom) =
    F.map (SheafOfModules.ιFree j.as) ≫
      ((originalPullbackFreeIso f I).hom ≫ originalFreeProjection X i)
  rw [← Category.assoc, ← F.map_comp (SheafOfModules.ιFree j.as) (originalFreeProjection Y i),
    originalFreeProjection_inclusion]
  rw [← Category.assoc, originalPullbackFreeIso_inclusion, Category.assoc,
    originalFreeProjection_inclusion]
  split_ifs <;> simp

/-- The actual matrix coefficient of an original native free-sheaf map. -/
def originalFreeHomCoefficient {X : Scheme.{u}} {I J : Type u} [DecidableEq J]
    (q : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J) (i : I) (j : J) :
    End (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.ιFree i ≫ q ≫ originalFreeProjection X j

/-- The actual true native pullback of the original map, in the same original free frames. -/
def originalPullbackFreeHom {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u}
    (q : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.free (R := Y.ringCatSheaf) J) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J :=
  (originalPullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map q ≫
    (originalPullbackFreeIso f J).hom

/-- Original inclusion and projection frame triangles preserve their actual original coefficient. -/
theorem originalConjugatedCoefficient {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U A B : C} {U' A' B' : D}
    (eU : F.obj U ≅ U') (eA : F.obj A ≅ A') (eB : F.obj B ≅ B')
    (i : U ⟶ A) (p : B ⟶ U) (q : A ⟶ B) (i' : U' ⟶ A') (p' : B' ⟶ U')
    (hi : F.map i ≫ eA.hom = eU.hom ≫ i')
    (hp : F.map p ≫ eU.hom = eB.hom ≫ p') :
    i' ≫ (eA.inv ≫ F.map q ≫ eB.hom) ≫ p' =
      eU.inv ≫ F.map (i ≫ q ≫ p) ≫ eU.hom := by
  apply (cancel_epi eU.hom).mp
  simp only [Category.assoc, eU.hom_inv_id_assoc]
  rw [← Category.assoc eU.hom i', ← hi]
  simp only [Category.assoc, eA.hom_inv_id_assoc]
  rw [← hp]
  simp only [F.map_comp, Category.assoc]

/-- The actual pulled-back coefficient is the true native pullback of the same original coefficient. -/
theorem originalPullbackFreeHom_coefficient {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I J : Type u} [DecidableEq J]
    (q : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.free (R := Y.ringCatSheaf) J) (i : I) (j : J) :
    originalFreeHomCoefficient (originalPullbackFreeHom f q) i j =
      originalPullbackUnitEnd f (originalFreeHomCoefficient q i j) :=
  originalConjugatedCoefficient (Scheme.Modules.pullback f)
    (originalPullbackUnitIso f) (originalPullbackFreeIso f I) (originalPullbackFreeIso f J)
    (SheafOfModules.ιFree i) (originalFreeProjection Y j) q (SheafOfModules.ιFree i)
    (originalFreeProjection X j) (originalPullbackFreeIso_inclusion f i)
    (originalPullbackFreeProjection f j)

/-- Every true native pulled-back original matrix coefficient has its precise original structural image. -/
theorem originalPullbackFreeHom_coefficient_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I J : Type u} [DecidableEq J]
    (q : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.free (R := Y.ringCatSheaf) J) (i : I) (j : J) (U : Y.Opens) :
    (originalFreeHomCoefficient (originalPullbackFreeHom f q) i j).val.app
      (.op (f ⁻¹ᵁ U)) (1 : Γ(X, f ⁻¹ᵁ U)) =
    f.app U ((originalFreeHomCoefficient q i j).val.app (.op U) (1 : Γ(Y, U))) := by
  rw [originalPullbackFreeHom_coefficient]
  exact originalPullbackUnitEnd_one f _ U

end Hironaka.Geometry.QuotGrassmann
