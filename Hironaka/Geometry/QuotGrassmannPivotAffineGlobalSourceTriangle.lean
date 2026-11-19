import Hironaka.Geometry.QuotGrassmannPivotAffineFreeSourceTriangle
import Hironaka.Geometry.QuotGrassmannPivotAffineGlobalBaseChange

/-!
# SAME global quotient has WHOLE ORIGINAL scalar source coordinates

The frozen original universal quotient coordinate frames, actual native affine
section comparison, and genuine coordinate scalar isomorphism satisfy the
entire source triangle and quotient square. Every compatibility is derived.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι] {A B : CommRingCat.{u}}

/-- The SAME ORIGINAL native universal quotient source-coordinate isomorphisms satisfy the WHOLE actual original scalar-extension triangle. -/
theorem originalGlobalAffineSourceSections_scalar_triangle (φ : A ⟶ B)
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (ModuleCat.extendScalars φ.hom).map
        (originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom ≫
      (originalGlobalAffineSourceSectionsBaseChangeIso R ι ν φ f).hom =
    (originalAffineFreeScalarCoordinateIso φ (ι ⊕ ν)).hom ≫
      (originalGlobalAffinePullbackSourceSectionsIso R ι ν (Spec.map φ ≫ f)).hom := by
  exact originalCompositeSpecFreeSourceScalarTriangle φ f (ι ⊕ ν)

private theorem originalSourceQuotientScalarDiagram {C : Type*} [Category C]
    {X Y Z W T U : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ U)
    (d : Y ⟶ W) (e : W ⟶ U) (s : X ⟶ T) (t : T ⟶ W)
    (hq : b ≫ c = d ≫ e) (hs : a ≫ d = s ≫ t) :
    (a ≫ b) ≫ c = s ≫ (t ≫ e) := by
  calc
    _ = a ≫ (b ≫ c) := Category.assoc _ _ _
    _ = a ≫ (d ≫ e) := congrArg (fun k => a ≫ k) hq
    _ = (a ≫ d) ≫ e := (Category.assoc _ _ _).symm
    _ = (s ≫ t) ≫ e := congrArg (fun k => k ≫ e) hs
    _ = _ := Category.assoc _ _ _

/-- SAME actual original linear quotient maps satisfy WHOLE native scalar extension with EXACT ORIGINAL coordinate source and actual produced target comparison. -/
theorem originalGlobalAffineQuotientSections_scalar_square (φ : A ⟶ B)
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (ModuleCat.extendScalars φ.hom).map
        (ModuleCat.ofHom (originalGlobalAffinePullbackQuotientSections R ι ν f)) ≫
      (originalGlobalAffineImageSectionsBaseChangeIso R ι ν φ f).hom =
    (originalAffineFreeScalarCoordinateIso φ (ι ⊕ ν)).hom ≫
      ModuleCat.ofHom (originalGlobalAffinePullbackQuotientSections R ι ν
        (Spec.map φ ≫ f)) := by
  let E := ModuleCat.extendScalars φ.hom
  have h := originalSourceQuotientScalarDiagram
    (E.map (originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom)
    (E.map (moduleSpecΓFunctor.map ((pullback f).map (originalGlobalQuotient R ι ν))))
    (originalGlobalAffineImageSectionsBaseChangeIso R ι ν φ f).hom
    (originalGlobalAffineSourceSectionsBaseChangeIso R ι ν φ f).hom
    (moduleSpecΓFunctor.map ((pullback (Spec.map φ ≫ f)).map
      (originalGlobalQuotient R ι ν)))
    (originalAffineFreeScalarCoordinateIso φ (ι ⊕ ν)).hom
    (originalGlobalAffinePullbackSourceSectionsIso R ι ν (Spec.map φ ≫ f)).hom
    (originalGlobalAffineQuotientSections_baseChange R ι ν φ f)
    (originalGlobalAffineSourceSections_scalar_triangle R ι ν φ f)
  change E.map ((originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom ≫
      moduleSpecΓFunctor.map ((pullback f).map (originalGlobalQuotient R ι ν))) ≫
    (originalGlobalAffineImageSectionsBaseChangeIso R ι ν φ f).hom =
      (originalAffineFreeScalarCoordinateIso φ (ι ⊕ ν)).hom ≫
        ((originalGlobalAffinePullbackSourceSectionsIso R ι ν (Spec.map φ ≫ f)).hom ≫
          moduleSpecΓFunctor.map ((pullback (Spec.map φ ≫ f)).map
            (originalGlobalQuotient R ι ν)))
  simpa only [Functor.map_comp] using h

end Hironaka.Geometry.QuotGrassmann
