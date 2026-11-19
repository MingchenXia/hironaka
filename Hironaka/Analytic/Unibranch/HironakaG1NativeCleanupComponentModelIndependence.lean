import Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupModelIndependence
import Hironaka.Analytic.Unibranch.HironakaG1NoncompactSmoothComponentModel
import Hironaka.Analytic.Unibranch.HironakaG1NativeDisjointCoproduct
import Hironaka.Resolution.HironakaNativePulledIdealComposition

/-! # Arbitrary-component native cleanup model-choice comparison

The ordinary inputs are two genuine component-manifold model collections.
Their terminal comparison is derived, including the empty component case.
The SAME native square transports the ENTIRE original singular ideal and
both literal structure-unit inclusions. No component is assumed to resolve
all of the original target. Blueprint is written first.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupComponentModelIndependence

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences
  Hironaka BlowupTowers HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealComposition HironakaSingularModuleSheafStalk
  HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  HironakaG1NativeCleanupModelIndependence

noncomputable section

variable {X Y : SourceReducedComplexSpace}

/-- ONLY an ordinary genuine full model of the ACTUAL native component. -/
structure ComponentModel (h : Y.IsSmooth) (c : ConnectedComponents Y.obj.left) where
  dimension : ℕ
  manifold : CMfd.{0} dimension
  model : wholeModel (n := dimension) manifold ≅ HironakaG1NoncompactSmoothComponentModel.componentObject h c

/-- Native smoothness internally supplies genuine model collections. -/
theorem exists_component_models (h : Y.IsSmooth) :
    Nonempty (∀ c : ConnectedComponents Y.obj.left, ComponentModel h c) := by
  classical
  have hmodels (c : ConnectedComponents Y.obj.left) : Nonempty (ComponentModel h c) := by
    obtain ⟨n, M, ⟨E⟩⟩ := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model h c
    exact ⟨⟨n, M, E⟩⟩
  exact ⟨fun c => Classical.choice (hmodels c)⟩

variable (p : Y ⟶ X) (hp : IsResolution p)

/-- Actual component thinness is derived from p, never from a false assertion
that each component map is a surjective resolution of all original X. -/
theorem componentThin (c : ConnectedComponents Y.obj.left) :
    interior ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p).hom.left.base ⁻¹'
      intrinsicSingularLocus X.obj) = ∅ := by
  obtain ⟨_, Z, _, _, hpre, hiso⟩ := hp.2
  have ht := hiso.interior_preimage_eq_empty hpre (interior_intrinsicSingularLocus_eq_empty X)
  have hj := HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hp.1 c
  have hs := hj.base_open.isOpenMap.preimage_interior_eq_interior_preimage
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base.hom.continuous
    (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)
  change interior ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base ⁻¹'
    (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅
  exact hs.symm.trans (by rw [ht, preimage_empty])

/-- The actual SAME-family terminal manifold of this component model. -/
def componentTerminal (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left) :
    CMfd.{0} (A c).dimension :=
  modelTerminal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p) (componentThin p hp c) (A c).model

/-- The full actual terminal projection followed by the original component inclusion. -/
def componentCleanupMap (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := (A c).dimension) (componentTerminal p hp A c) ⟶ Y :=
  modelCleanupMap (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p) (componentThin p hp c) (A c).model ≫
    HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c

/-- The genuine arbitrary native coproduct, with no cardinality restriction. -/
def cleanupSource (A : ∀ c, ComponentModel hp.1 c) : SourceReducedComplexSpace :=
  HironakaG1NativeDisjointCoproduct.coproduct (fun c => wholeModel (n := (A c).dimension) (componentTerminal p hp A c))

/-- Its full native projection to the original smooth resolution source. -/
def cleanupProjection (A : ∀ c, ComponentModel hp.1 c) : cleanupSource p hp A ⟶ Y :=
  HironakaG1NativeDisjointCoproduct.desc _ (componentCleanupMap p hp A)

/-- The SAME original composite to X. -/
def cleanupMorphism (A : ∀ c, ComponentModel hp.1 c) : cleanupSource p hp A ⟶ X :=
  cleanupProjection p hp A ≫ p

/-- ENTIRE native original-Sing total ideal, with its actual original scalar map. -/
def totalIdealModule (A : ∀ c, ComponentModel hp.1 c) :
    SheafOfModules.{0} (forgetRing (cleanupSource p hp A).obj.left.toSheafedSpace.sheaf) :=
  nativePulledIdealModule (cleanupMorphism p hp A).hom.left
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj))

/-- The literal inclusion of that entire ideal into the original structure-unit. -/
def totalIdealInclusion (A : ∀ c, ComponentModel hp.1 c) :
    totalIdealModule p hp A ⟶
      SheafOfModules.unit (forgetRing (cleanupSource p hp A).obj.left.toSheafedSpace.sheaf) :=
  nativePulledIdealInclusion (cleanupMorphism p hp A).hom.left
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj))

private def coproductIso {ι : Type} {Z W : ι → SourceReducedComplexSpace}
    (e : ∀ i, Z i ≅ W i) : HironakaG1NativeDisjointCoproduct.coproduct Z ≅ HironakaG1NativeDisjointCoproduct.coproduct W where
  hom := HironakaG1NativeDisjointCoproduct.desc Z (fun i => (e i).hom ≫ HironakaG1NativeDisjointCoproduct.inclusion W i)
  inv := HironakaG1NativeDisjointCoproduct.desc W (fun i => (e i).inv ≫ HironakaG1NativeDisjointCoproduct.inclusion Z i)
  hom_inv_id := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext
    intro i
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
      HironakaG1NativeDisjointCoproduct.inclusion_desc, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext
    intro i
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
      HironakaG1NativeDisjointCoproduct.inclusion_desc, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id]

private theorem coproductIso_desc {ι : Type} {Z W : ι → SourceReducedComplexSpace}
    (e : ∀ i, Z i ≅ W i) (F : ∀ i, Z i ⟶ Y) (G : ∀ i, W i ⟶ Y)
    (he : ∀ i, (e i).hom ≫ G i = F i) :
    (coproductIso e).hom ≫ HironakaG1NativeDisjointCoproduct.desc W G =
      HironakaG1NativeDisjointCoproduct.desc Z F := by
  apply HironakaG1NativeDisjointCoproduct.hom_ext
  intro i
  change HironakaG1NativeDisjointCoproduct.inclusion Z i ≫
    (HironakaG1NativeDisjointCoproduct.desc Z (fun j => (e j).hom ≫
      HironakaG1NativeDisjointCoproduct.inclusion W j) ≫
      HironakaG1NativeDisjointCoproduct.desc W G) =
    HironakaG1NativeDisjointCoproduct.inclusion Z i ≫ HironakaG1NativeDisjointCoproduct.desc Z F
  rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
    HironakaG1NativeDisjointCoproduct.inclusion_desc, HironakaG1NativeDisjointCoproduct.inclusion_desc]
  exact he i

/-- Full native comparison of ANY two actual component model collections.
The empty index case uses the same genuine coproduct uniqueness equations. -/
theorem exists_cleanup_comparison
    (A B : ∀ c, ComponentModel hp.1 c) :
    ∃ e : cleanupSource p hp A ≅ cleanupSource p hp B,
      e.hom ≫ cleanupProjection p hp B = cleanupProjection p hp A ∧
      e.hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A ∧
      e.hom.hom.left.base ⁻¹'
          ((cleanupMorphism p hp B).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
        (cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicRegularLocus X.obj := by
  classical
  have hcomp (c : ConnectedComponents Y.obj.left) :
      ∃ e : wholeModel (n := (A c).dimension) (componentTerminal p hp A c) ≅
          wholeModel (n := (B c).dimension) (componentTerminal p hp B c),
        e.hom ≫ componentCleanupMap p hp B c = componentCleanupMap p hp A c := by
    let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hp.1 c).obj.left :=
      isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected c)
    obtain ⟨η, e, he, hs, hx, hr, hi⟩ := exists_cleanup_model_comparison_of_thin
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p) (componentThin p hp c) (A c).model (B c).model
    refine ⟨e, ?_⟩
    change e.hom ≫ (_ ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c) =
      _ ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c
    rw [← Category.assoc, hs]
  choose e he using hcomp
  let E := coproductIso e
  have hY : E.hom ≫ cleanupProjection p hp B = cleanupProjection p hp A := by
    exact coproductIso_desc e (componentCleanupMap p hp A) (componentCleanupMap p hp B) he
  have hX : E.hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A := by
    change E.hom ≫ (cleanupProjection p hp B ≫ p) = cleanupProjection p hp A ≫ p
    rw [← Category.assoc, hY]
  refine ⟨E, hY, hX, ?_⟩
  ext z
  have hz := congrArg (fun f : cleanupSource p hp A ⟶ X => f.hom.left.base z) hX
  change (cleanupMorphism p hp B).hom.left.base (E.hom.hom.left.base z) =
    (cleanupMorphism p hp A).hom.left.base z at hz
  exact iff_of_eq (congrArg (fun x => x ∈ intrinsicRegularLocus X.obj) hz)

private theorem totalIdealSubmodule_eq
    (A B : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p hp A ≅ cleanupSource p hp B)
    (hs : e.hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A) :
    nativePulledIdealSubmodule e.hom.hom.left (totalIdealModule p hp B)
      (totalIdealInclusion p hp B) =
    nativePulledIdealSubmodule (cleanupMorphism p hp A).hom.left
      (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
      (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) := by
  have hF : e.hom.hom.left ≫ (cleanupMorphism p hp B).hom.left =
      (cleanupMorphism p hp A).hom.left := congrArg (fun f => f.hom.left) hs
  change nativePulledIdealSubmodule e.hom.hom.left
    (nativePulledIdealModule (cleanupMorphism p hp B).hom.left _ _)
    (nativePulledIdealInclusion (cleanupMorphism p hp B).hom.left _ _) =
    nativePulledIdealSubmodule (cleanupMorphism p hp A).hom.left _ _
  rw [submodule_comp, hF]

/-- ENTIRE native total-ideal transport from the SAME full native square. -/
def totalIdealIso_of_square
    (A B : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p hp A ≅ cleanupSource p hp B)
    (hs : e.hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A) :
    nativePulledIdealModule e.hom.hom.left (totalIdealModule p hp B)
      (totalIdealInclusion p hp B) ≅ totalIdealModule p hp A where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (totalIdealSubmodule_eq p hp A B e hs).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (totalIdealSubmodule_eq p hp A B e hs).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

/-- Forward triangle with the literal original structure-unit inclusions. -/
theorem totalIdealIso_hom_comp_inclusion
    (A B : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p hp A ≅ cleanupSource p hp B)
    (hs : e.hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A) :
    (totalIdealIso_of_square p hp A B e hs).hom ≫ totalIdealInclusion p hp A =
      nativePulledIdealInclusion e.hom.hom.left (totalIdealModule p hp B)
        (totalIdealInclusion p hp B) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (totalIdealSubmodule_eq p hp A B e hs).le

/-- Inverse triangle, retaining the SAME full original scalar inclusions. -/
theorem totalIdealIso_inv_comp_inclusion
    (A B : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p hp A ≅ cleanupSource p hp B)
    (hs : e.hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A) :
    (totalIdealIso_of_square p hp A B e hs).inv ≫
        nativePulledIdealInclusion e.hom.hom.left (totalIdealModule p hp B)
          (totalIdealInclusion p hp B) = totalIdealInclusion p hp A := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (totalIdealSubmodule_eq p hp A B e hs).ge

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupComponentModelIndependence
