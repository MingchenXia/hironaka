import Hironaka.Geometry.QuotGrassmannPivotAffineMatrixSections
import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackCanonical

/-!
# SAME original polynomial-pivot quotient on actual native affine sections

Both maps of the actual unframed pullback target are produced. The EXACT
original coordinate-source quotient is the SAME normalized polynomial matrix.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot


universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalCoordinateSectionQuotientDiagram {C : Type*} [Category C]
    {A S T M N K : C} (a : A ⟶ S) (b : S ⟶ T) (q : T ⟶ M)
    (e : M ⟶ N) (c : K ≅ N) (m : S ⟶ N) (l : A ⟶ K)
    (hq : b ≫ q ≫ e = m) (hm : a ≫ m = l ≫ c.hom) :
    (a ≫ b ≫ q) ≫ (e ≫ c.inv) = l := by
  calc
    _ = (a ≫ (b ≫ q ≫ e)) ≫ c.inv := by simp only [Category.assoc]
    _ = (a ≫ m) ≫ c.inv := congrArg (fun k => (a ≫ k) ≫ c.inv) hq
    _ = (l ≫ c.hom) ≫ c.inv := congrArg (fun k => k ≫ c.inv) hm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- BOTH actual native linear maps from SAME unframed original pivot pullback sections to the original normalized coordinate target. -/
def originalGlobalAffinePivotSectionsTargetIso :
    (moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))).obj ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).obj
      (originalGlobalImageQuotient R ι ν)) ≅
      ModuleCat.of (ChartRing R ι κ) (ι → ChartRing R ι κ) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))).mapIso
    (originalGlobalImagePivotTruePullbackFrame R e) ≪≫
    (originalAffineFreeSectionsCoordinateIso (.of (ChartRing R ι κ)) ι).symm

/-- The WHOLE exact original affine quotient on SAME native polynomial pivot reads as its ORIGINAL split normalized matrix linear map. -/
theorem originalGlobalAffinePivotSectionsTargetIso_quotient :
    ((originalGlobalAffinePullbackSourceSectionsIso R ι ν
        (A := CommRingCat.of (ChartRing R ι κ)) (originalPivotModelMorphism R e)).hom ≫
      (moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))).map
        ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).map
          (originalGlobalQuotient R ι ν))) ≫
      (originalGlobalAffinePivotSectionsTargetIso R e).hom =
    ModuleCat.ofHom (pivotUniversalMatrix R e).mulVecLin := by
  let f := originalPivotModelMorphism R e
  let G := moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))
  let s := originalPullbackFreeIso f (ι ⊕ ν)
  let t := originalGlobalImagePivotTruePullbackFrame R e
  let q := (Scheme.Modules.pullback f).map (originalGlobalQuotient R ι ν)
  let M := originalMatrixQuotientSheaf (ChartRing R ι κ) (pivotUniversalMatrix R e)
  have hs := congrArg Iso.inv
    (originalGlobalSourcePivotTruePullbackFrame_eq_originalPullbackFreeIso R e)
  have hq : s.inv ≫ q ≫ t.hom = M :=
    (congrArg (fun k => k ≫ q ≫ t.hom) hs.symm).trans
      (originalGlobalImagePivotFramedQuotient_eq_originalMatrix R e)
  have hg := congrArg G.map hq
  simp only [Functor.map_comp] at hg
  have h := originalCoordinateSectionQuotientDiagram
    (originalAffineFreeSectionsCoordinateIso (.of (ChartRing R ι κ)) (ι ⊕ ν)).hom
    (G.map s.inv) (G.map q) (G.map t.hom)
    (originalAffineFreeSectionsCoordinateIso (.of (ChartRing R ι κ)) ι)
    (G.map M) (ModuleCat.ofHom (pivotUniversalMatrix R e).mulVecLin) hg
    (originalAffineMatrixQuotientSheaf_sections (ChartRing R ι κ) (pivotUniversalMatrix R e))
  exact h

/-- The reverse WHOLE original quotient triangle lands in the SAME actual unframed native pivot pullback section module. -/
theorem originalGlobalAffinePivotSectionsTargetIso_quotient_inv :
    ModuleCat.ofHom (pivotUniversalMatrix R e).mulVecLin ≫
      (originalGlobalAffinePivotSectionsTargetIso R e).inv =
    (originalGlobalAffinePullbackSourceSectionsIso R ι ν
        (A := CommRingCat.of (ChartRing R ι κ)) (originalPivotModelMorphism R e)).hom ≫
      (moduleSpecΓFunctor (R := CommRingCat.of (ChartRing R ι κ))).map
        ((Scheme.Modules.pullback (originalPivotModelMorphism R e)).map
          (originalGlobalQuotient R ι ν)) := by
  have h := congrArg (fun k => k ≫ (originalGlobalAffinePivotSectionsTargetIso R e).inv)
    (originalGlobalAffinePivotSectionsTargetIso_quotient R e)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

end Hironaka.Geometry.QuotGrassmann
