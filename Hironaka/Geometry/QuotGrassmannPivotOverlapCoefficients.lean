import Hironaka.Geometry.QuotGrassmannPivotOverlapMorphisms
import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackSections

/-!
# BOTH actual original overlap maps have the SAME entire original scalar coefficients

This follows from the actual original scheme-to-model/base triangles and
native spectrum faithfulness, not an assumed coefficient compatibility.
-/

noncomputable section

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι ν : Type u}
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  (p t : (ι ⊕ ν) ≃ (ι ⊕ ν))

/-- The WHOLE ORIGINAL scalar coefficient ring maps of BOTH actual native overlap polynomial charts coincide, derived from their actual scheme-to-model/base triangles. -/
theorem originalOverlapPolynomialMaps_coeff_eq :
    (pivotOverlapPolynomialMap R p (pivotIndex (coordinateSelector ι ν) t)).comp
      (algebraMap R (ChartRing R ι ν)) =
    (pivotOverlapRightPolynomialMap R p t).comp (algebraMap R (ChartRing R ι ν)) := by
  have hl := originalOverlapLeftMorphism_triangle R p t
  change originalOverlapLeftMorphism R p t ≫ originalPivotModelMorphism R p =
    originalOverlapModelMorphism R p t at hl
  have hr := originalOverlapRightMorphism_triangle R p t
  change originalOverlapRightMorphism R p t ≫ originalPivotModelMorphism R t =
    originalOverlapModelMorphism R p t at hr
  have hs := congrArg (fun f => f ≫ projectiveStructure R ι ν) (hl.trans hr.symm)
  simp only [Category.assoc, originalPivotModelMorphism_structure] at hs
  have hm : CommRingCat.ofHom
      ((pivotOverlapPolynomialMap R p (pivotIndex (coordinateSelector ι ν) t)).comp
        (algebraMap R (ChartRing R ι ν))) = CommRingCat.ofHom
      ((pivotOverlapRightPolynomialMap R p t).comp (algebraMap R (ChartRing R ι ν))) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R ι ν)) ≫
      CommRingCat.ofHom (pivotOverlapPolynomialMap R p (pivotIndex (coordinateSelector ι ν) t))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R ι ν)) ≫
        CommRingCat.ofHom (pivotOverlapRightPolynomialMap R p t))
    rw [Spec.map_comp, Spec.map_comp]
    exact hs
  exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of
    (PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) p)
      (pivotIndex (coordinateSelector ι ν) t)) => f.hom) hm

end Hironaka.Geometry.QuotGrassmann
