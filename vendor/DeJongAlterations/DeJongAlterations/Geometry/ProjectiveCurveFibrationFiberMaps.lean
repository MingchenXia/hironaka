import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Actual fibre maps induced by open immersions -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.ProjectiveCurveFibration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X Y Z : Scheme.{u}}

/-- Composition with an actual target open immersion preserves its native fibres. -/
def fiberCompOpenImmersionIso (f : X ⟶ Y) (c : Y ⟶ Z) [IsOpenImmersion c] (y : Y) :
    f.fiber y ≅ (f ≫ c).fiber (c y) := by
  have h : IsPullback (𝟙 X) f (f ≫ c) c :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  let m : f.fiber y ⟶ (f ≫ c).fiber (c y) :=
    pullback.map f (Y.fromSpecResidueField y) (f ≫ c) (Z.fromSpecResidueField (c y))
      (𝟙 X) (Spec.map (c.residueFieldMap y)) c
    h.w.symm (by simp)
  have hp : IsPullback m (f.fiberToSpecResidueField y)
      ((f ≫ c).fiberToSpecResidueField (c y)) (Spec.map (c.residueFieldMap y)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h y
  have : IsIso m := hp.isIso_fst_of_isIso
  exact asIso m

/-- The actual fibre map induced by a source morphism over an unchanged target. -/
def sourceFiberMap (j : U ⟶ X) (f : X ⟶ Y) (y : Y) : (j ≫ f).fiber y ⟶ f.fiber y :=
  pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem sourceFiberMap_fiberι (j : U ⟶ X) (f : X ⟶ Y) (y : Y) :
    sourceFiberMap j f y ≫ f.fiberι y = (j ≫ f).fiberι y ≫ j := by
  simp [sourceFiberMap, Scheme.Hom.fiberι]

/-- The actual induced fibre map is the actual base change of the source morphism. -/
theorem sourceFiberMap_isPullback (j : U ⟶ X) (f : X ⟶ Y) (y : Y) :
    IsPullback (sourceFiberMap j f y) ((j ≫ f).fiberι y) (f.fiberι y) j := by
  have hs : IsPullback (sourceFiberMap j f y ≫ f.fiberToSpecResidueField y)
      ((j ≫ f).fiberι y) (Y.fromSpecResidueField y) (j ≫ f) := by
    simpa [sourceFiberMap, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι] using
      (IsPullback.of_hasPullback (j ≫ f) (Y.fromSpecResidueField y)).flip
  exact hs.of_right (sourceFiberMap_fiberι j f y)
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip

instance sourceFiberMap_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (y : Y) : IsOpenImmersion (sourceFiberMap j f y) := by
  apply MorphismProperty.of_isPullback (sourceFiberMap_isPullback j f y).flip
  infer_instance

end DeJongAlterations.Geometry.ProjectiveCurveFibration
