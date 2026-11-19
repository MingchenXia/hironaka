import Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanupCore
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothManifoldReflection

/-! # Actual component and manifold maps of ordinary native smooth arrows

The component INDEX MAP, full native component factor, scalar square and
actual manifold submersion are all DERIVED. No component assignment,
comparison, model correctness or ambient submersion packet is input.
Blueprint precedes source. C18 reflection/locality is reused unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothComponentMap

open Hironaka Hironaka
  HironakaEmbeddedNativeMorphism SourceReducedComplexSpace OriginalNativeModification
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothOpenLocality
  HironakaG1NativeCleanupComponentModelIndependence

noncomputable section

variable {Y Y' : SourceReducedComplexSpace}

/-- The natural ACTUAL component map, with no bijectivity/surjectivity hypothesis. -/
def componentIndex (g : Y' ⟶ Y) : ConnectedComponents Y'.obj.left → ConnectedComponents Y.obj.left :=
  Quotient.map g.hom.left.base (by
    intro x y hxy
    change connectedComponent (g.hom.left.base x) = connectedComponent (g.hom.left.base y)
    have hy : y ∈ connectedComponent x := by
      rw [show connectedComponent x = connectedComponent y from hxy]
      exact mem_connectedComponent
    exact connectedComponent_eq
      (g.hom.left.base.hom.continuous.image_connectedComponent_subset x ⟨y, hy, rfl⟩))

/-- The literal original-point formula, including empty sources. -/
theorem componentIndex_mk (g : Y' ⟶ Y) (y : Y'.obj.left) :
    componentIndex g (ConnectedComponents.mk y) = ConnectedComponents.mk (g.hom.left.base y) := rfl

private def nativeOpenLift {A B C : SourceReducedComplexSpace}
    (i : B ⟶ C) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (f : A ⟶ C)
    (hr : range f.hom.left.base ⊆ range i.hom.left.base) : A ⟶ B := by
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left f.hom.left hr
  have hfac : l ≫ i.hom.left = f.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hp : l ≫ B.obj.hom = A.obj.hom := by
    calc
      _ = l ≫ (i.hom.left ≫ C.obj.hom) := congrArg (fun t => l ≫ t) (Over.w i.hom).symm
      _ = (l ≫ i.hom.left) ≫ C.obj.hom := (Category.assoc _ _ _).symm
      _ = f.hom.left ≫ C.obj.hom := congrArg (fun t => t ≫ C.obj.hom) hfac
      _ = _ := Over.w f.hom
  exact ObjectProperty.homMk (Over.homMk l hp)

private theorem nativeOpenLift_fac {A B C : SourceReducedComplexSpace}
    (i : B ⟶ C) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (f : A ⟶ C)
    (hr : range f.hom.left.base ⊆ range i.hom.left.base) :
    nativeOpenLift i hi f hr ≫ i = f := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac i.hom.left f.hom.left hr

private theorem componentRange (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (c : ConnectedComponents Y'.obj.left) :
    range (HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c ≫ g).hom.left.base ⊆
      range (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c)).hom.left.base := by
  rw [HironakaG1NoncompactSmoothComponentModel.componentInclusion_range]
  rintro _ ⟨z, rfl⟩
  change ConnectedComponents.mk (g.hom.left.base z.val) = componentIndex g c
  rw [← componentIndex_mk g z.val, z.property]

/-- Full original native factor through the ACTUAL target component OI. -/
def componentMap (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (c : ConnectedComponents Y'.obj.left) :
    HironakaG1NoncompactSmoothComponentModel.componentObject h' c ⟶
      HironakaG1NoncompactSmoothComponentModel.componentObject h (componentIndex g c) :=
  nativeOpenLift
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c))
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion h (componentIndex g c))
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c ≫ g) (componentRange h' h g c)

/-- SAME full original inclusion/scalar square, not just a point/support formula. -/
theorem componentMap_square (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (c : ConnectedComponents Y'.obj.left) :
    componentMap h' h g c ≫
        HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c) =
      HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c ≫ g :=
  nativeOpenLift_fac _ _ _ (componentRange h' h g c)

/-- Genuine native smoothness of the ACTUAL component arrow is derived. -/
theorem componentMap_isSmooth (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (hg : IsSmoothMorphism g) (c : ConnectedComponents Y'.obj.left) :
    IsSmoothMorphism (componentMap h' h g c) :=
  isSmoothMorphism_of_open_square
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c)
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c))
    (componentMap h' h g c) g
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion h' c)
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion h (componentIndex g c))
    (componentMap_square h' h g c).symm hg

/-- Actual full native map between ANY independently constructed genuine models. -/
def modelMap (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (A' : ∀ c, ComponentModel h' c) (A : ∀ c, ComponentModel h c)
    (c : ConnectedComponents Y'.obj.left) :
    wholeModel (n := (A' c).dimension) (A' c).manifold ⟶
      wholeModel (n := (A (componentIndex g c)).dimension) (A (componentIndex g c)).manifold :=
  (A' c).model.hom ≫ componentMap h' h g c ≫ (A (componentIndex g c)).model.inv

/-- The full original square of THAT SAME model map over the actual g. -/
theorem modelMap_square (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (A' : ∀ c, ComponentModel h' c) (A : ∀ c, ComponentModel h c)
    (c : ConnectedComponents Y'.obj.left) :
    modelMap h' h g A' A c ≫ ((A (componentIndex g c)).model.hom ≫
        HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c)) =
      ((A' c).model.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c) ≫ g := by
  simp only [modelMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [componentMap_square]

/-- Actual model-map smoothness from the original native arrow and true OI square. -/
theorem modelMap_isSmooth (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (hg : IsSmoothMorphism g) (A' : ∀ c, ComponentModel h' c) (A : ∀ c, ComponentModel h c)
    (c : ConnectedComponents Y'.obj.left) : IsSmoothMorphism (modelMap h' h g A' A c) := by
  let i := (A' c).model.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c
  let j := (A (componentIndex g c)).model.hom ≫
    HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c)
  have hi : LocallyRingedSpace.IsOpenImmersion i.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion ((A' c).model.hom.hom.left ≫
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c).hom.left)
    infer_instance
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion ((A (componentIndex g c)).model.hom.hom.left ≫
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentIndex g c)).hom.left)
    infer_instance
  exact isSmoothMorphism_of_open_square i j (modelMap h' h g A' A c) g hi hj
    (modelMap_square h' h g A' A c).symm hg

/-- The LITERAL original point map of the ACTUAL native model arrow. -/
def modelPointMap (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (A' : ∀ c, ComponentModel h' c) (A : ∀ c, ComponentModel h c)
    (c : ConnectedComponents Y'.obj.left) : (A' c).manifold → (A (componentIndex g c)).manifold :=
  OriginalNativeManifoldOpenImage.pointMap (modelMap h' h g A' A c)

/-- Ordinary native smoothness INTERNALLY yields the genuine global manifold submersion. -/
theorem modelPointMap_isSubmersion (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (hg : IsSmoothMorphism g) (A' : ∀ c, ComponentModel h' c) (A : ∀ c, ComponentModel h c)
    (c : ConnectedComponents Y'.obj.left) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (A' c).dimension)
      𝓘(ℂ, ComplexModel (A (componentIndex g c)).dimension) ∞ (modelPointMap h' h g A' A c) :=
  OriginalNativeSmoothManifoldReflection.pointMap_isSubmersion (modelMap h' h g A' A c)
    (modelMap_isSmooth h' h g hg A' A c)

/-- The induced native map is ENTIRELY the SAME original model arrow, with all scalars. -/
theorem nativeMorphism_modelPointMap (h' : Y'.IsSmooth) (h : Y.IsSmooth) (g : Y' ⟶ Y)
    (hg : IsSmoothMorphism g) (A' : ∀ c, ComponentModel h' c) (A : ∀ c, ComponentModel h c)
    (c : ConnectedComponents Y'.obj.left) :
    nativeMorphism (modelPointMap_isSubmersion h' h g hg A' A c).contMDiff = modelMap h' h g A' A c :=
  OriginalNativeManifoldOpenImage.nativeMorphism_pointMap (modelMap h' h g A' A c)

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothComponentMap
