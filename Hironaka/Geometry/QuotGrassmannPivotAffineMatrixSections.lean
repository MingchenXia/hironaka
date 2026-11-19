import Hironaka.Geometry.QuotGrassmannPivotAffineFreeSections
import Hironaka.Geometry.QuotGrassmannPivotOverlapSheaf

/-!
# SAME original affine matrix sheaf gives its WHOLE original section matrix

The exact original affine coordinate frames are retained. Genuine native
tilde--Gamma unit naturality proves the entire matrix-section triangle.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalSectionCoordinateDiagram {C : Type*} [Category C]
    {A B U V S T : C} (s : U ≅ S) (t : V ≅ T)
    (a : A ⟶ U) (b : B ⟶ V) (q : A ⟶ B) (h : U ⟶ V)
    (hn : a ≫ h = q ≫ b) :
    (a ≫ s.hom) ≫ (s.inv ≫ h ≫ t.hom) = q ≫ b ≫ t.hom := by
  calc
    _ = (a ≫ h) ≫ t.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (q ≫ b) ≫ t.hom := congrArg (fun k => k ≫ t.hom) hn
    _ = _ := Category.assoc _ _ _

/-- The WHOLE actual original matrix sheaf map intertwines EXACT original finite-coordinate section frames with its SAME original matrix linear map. -/
theorem originalAffineMatrixQuotientSheaf_sections (B : Type u) [CommRing B]
    {I E : Type u} [Finite I] [Fintype E] (M : Matrix I E B) :
    (originalAffineFreeSectionsCoordinateIso (.of B) E).hom ≫
        moduleSpecΓFunctor.map (originalMatrixQuotientSheaf B M) =
      ModuleCat.ofHom M.mulVecLin ≫
        (originalAffineFreeSectionsCoordinateIso (.of B) I).hom := by
  let V := ModuleCat.of B (E → B)
  let W := ModuleCat.of B (I → B)
  let q : V ⟶ W := ModuleCat.ofHom M.mulVecLin
  let F := tilde.functor (.of B)
  let G := moduleSpecΓFunctor (R := CommRingCat.of B)
  let s := coordinateSheafIsoFree B E
  let t := coordinateSheafIsoFree B I
  have hn : q ≫ (tilde.isoTop (R := CommRingCat.of B) W).hom =
      (tilde.isoTop (R := CommRingCat.of B) V).hom ≫ G.map (F.map q) :=
    (tilde.toOpen_map_app (R := CommRingCat.of B) q ⊤).symm
  have h := originalSectionCoordinateDiagram (G.mapIso s) (G.mapIso t)
    (tilde.isoTop (R := CommRingCat.of B) V).hom (tilde.isoTop (R := CommRingCat.of B) W).hom q
    (G.map (F.map q)) hn.symm
  change ((tilde.isoTop (R := CommRingCat.of B) V).hom ≫ G.map s.hom) ≫ G.map (s.inv ≫ F.map q ≫ t.hom) =
    q ≫ (tilde.isoTop (R := CommRingCat.of B) W).hom ≫ G.map t.hom
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv] using h

end Hironaka.Geometry.QuotGrassmann
