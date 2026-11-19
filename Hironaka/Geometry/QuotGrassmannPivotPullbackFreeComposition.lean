import Hironaka.Geometry.QuotGrassmannPivotPullbackUnitCoherence
import Hironaka.Geometry.QuotGrassmannPivotPullbackFree

/-!
# ORIGINAL canonical native free-pullback frames compose exactly

Every original basis inclusion is retained. The existing actual original unit
composition theorem and native pullback-composition naturality derive the whole
free-frame comparison, without an assumed source-coordinate compatibility.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original inverse free-pullback frame preserves the actual inverse unit and ORIGINAL basis inclusion. -/
theorem originalPullbackFreeIso_inverse_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} (i : I) :
    (originalPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) =
      SheafOfModules.ιFree i ≫ (originalPullbackFreeIso f I).inv := by
  apply (cancel_mono (originalPullbackFreeIso f I).hom).mp
  simp only [Category.assoc, originalPullbackFreeIso_inclusion,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem originalFreeCompositionDiagram {C : Type*} [Category C]
    {A B D E F G H K : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (u : A ⟶ G) (v : G ⟶ D) (w : G ⟶ H) (x : H ⟶ E)
    (y : H ⟶ K) (i : K ⟶ F) (z : A ⟶ K) (r : B ⟶ F)
    (h₁ : a ≫ b = u ≫ v) (h₂ : v ≫ c = w ≫ x)
    (h₃ : x ≫ d = y ≫ i) (h₄ : u ≫ w ≫ y = z) (h₅ : a ≫ r = z ≫ i) :
    a ≫ b ≫ c ≫ d = a ≫ r := by
  calc
    _ = (a ≫ b) ≫ c ≫ d := by simp only [Category.assoc]
    _ = (u ≫ v) ≫ c ≫ d := congrArg (fun k => k ≫ c ≫ d) h₁
    _ = u ≫ (v ≫ c) ≫ d := by simp only [Category.assoc]
    _ = u ≫ (w ≫ x) ≫ d := congrArg (fun k => u ≫ k ≫ d) h₂
    _ = u ≫ w ≫ (x ≫ d) := by simp only [Category.assoc]
    _ = u ≫ w ≫ (y ≫ i) := congrArg (fun k => u ≫ w ≫ k) h₃
    _ = (u ≫ w ≫ y) ≫ i := by simp only [Category.assoc]
    _ = z ≫ i := congrArg (fun k => k ≫ i) h₄
    _ = _ := h₅.symm

/-- The WHOLE ORIGINAL canonical finite or infinite free-pullback frame satisfies exact native inverse-composition coherence. -/
theorem originalPullbackFreeIso_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Type u) :
    ((Scheme.Modules.pullbackComp f g).app
        (SheafOfModules.free (R := Z.ringCatSheaf) I)).inv ≫
      (Scheme.Modules.pullback f).map (originalPullbackFreeIso g I).hom ≫
        (originalPullbackFreeIso f I).hom = (originalPullbackFreeIso (f ≫ g) I).hom := by
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback g
  let H := Scheme.Modules.pullback (f ≫ g)
  let c := Scheme.Modules.pullbackComp f g
  let L := SheafOfModules.unit Z.ringCatSheaf
  let S := SheafOfModules.free (R := Z.ringCatSheaf) I
  let : PreservesColimits H := by dsimp [H]; infer_instance
  apply (isColimitOfPreserves H
    (SheafOfModules.isColimitFreeCofan (R := Z.ringCatSheaf) I)).hom_ext
  intro i
  have hn : H.map (SheafOfModules.ιFree (R := Z.ringCatSheaf) i.as) ≫ c.inv.app S =
      c.inv.app L ≫ F.map (G.map (SheafOfModules.ιFree i.as)) :=
    c.inv.naturality (SheafOfModules.ιFree i.as)
  have hgm : F.map (G.map (SheafOfModules.ιFree (R := Z.ringCatSheaf) i.as)) ≫
      F.map (originalPullbackFreeIso g I).hom =
    F.map (originalPullbackUnitIso g).hom ≫ F.map (SheafOfModules.ιFree i.as) := by
    have h := congrArg F.map (originalPullbackFreeIso_inclusion g i.as)
    simp only [Functor.map_comp] at h
    exact h
  exact originalFreeCompositionDiagram
    (H.map (SheafOfModules.ιFree i.as)) (c.inv.app S)
    (F.map (originalPullbackFreeIso g I).hom) (originalPullbackFreeIso f I).hom
    (c.inv.app L) (F.map (G.map (SheafOfModules.ιFree i.as)))
    (F.map (originalPullbackUnitIso g).hom) (F.map (SheafOfModules.ιFree i.as))
    (originalPullbackUnitIso f).hom (SheafOfModules.ιFree i.as)
    (originalPullbackUnitIso (f ≫ g)).hom (originalPullbackFreeIso (f ≫ g) I).hom
    hn hgm (originalPullbackFreeIso_inclusion f i.as)
    (originalPullbackUnitIso_comp_inv f g) (originalPullbackFreeIso_inclusion (f ≫ g) i.as)

end Hironaka.Geometry.QuotGrassmann
