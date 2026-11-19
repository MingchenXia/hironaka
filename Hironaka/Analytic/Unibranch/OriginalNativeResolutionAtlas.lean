import Hironaka.Analytic.Unibranch.OriginalNativeProperAtlas
import Hironaka.Analytic.Unibranch.OriginalAnalyticCover
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Analytic.Unibranch.HironakaG11ModificationCalculus

/-! Genuine resolution readouts on the SAME ordinary proper native atlas.
Local resolutions and genuine LOCAL original-Reg protection are inputs.
Global source smoothness, full original-Reg IsIsoOver, original-Sing inverse
thinness, the resolution and surjectivity are derived, with arbitrary overlaps.
Blueprint first: `original-native-resolution-atlas.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeResolutionAtlas
noncomputable section
open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11IntrinsicRegularOpenImmersion SourceReducedComplexSpace OriginalNativeProperAtlas

variable (D : LocallyRingedSpace.GlueData.{0})
  (σ : ∀ i : D.J, D.U i ⟶ complexPoint)
  (hA : ∀ i, sourceReducedComplexSpaceProperty (Over.mk (σ i)))
  {X : SourceReducedComplexSpace} {B : D.J → SourceReducedComplexSpace}
  (J : ∀ i, B i ⟶ X) (p : ∀ i, localSource D σ hA i ⟶ B i)
  (hover : ∀ i j, D.f i j ≫ localProjection D σ hA J p i =
    (D.t i j ≫ D.f j i) ≫ localProjection D σ hA J p j)
  (hOverlap : ∀ i j, range (D.f i j).base =
    (localProjection D σ hA J p i).base ⁻¹' range (J j).hom.left.base)
  (hJ : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left)
  (hcover : ∀ x : X.obj.left, ∃ (i : D.J) (b : (B i).obj.left), (J i).hom.left.base b = x)
  (hres : ∀ i, IsResolution (p i))

local notation "Z" => sourceObject D σ hA J p hover hOverlap hJ hcover (fun i => And.left (And.right (hres i)))
local notation "F" => projectionMorphism D σ hA J p hover hOverlap hJ hcover (fun i => And.left (And.right (hres i)))
local notation "L" => localMorphism D σ hA J p hover hOverlap hJ hcover (fun i => And.left (And.right (hres i)))

/-- Smoothness is read on actual full native charts of the SAME glued source. -/
theorem source_isSmooth : (Z).IsSmooth := by
  intro x
  obtain ⟨i,y,hy⟩ := localMorphism_cover D σ hA J p hover hOverlap hJ hcover
    (fun i => And.left (And.right (hres i))) x
  obtain ⟨d,V,k,hk,hks,z,hz⟩ := (hres i).1 y
  refine ⟨d,V,k ≫ (L i).hom.left,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k hk _
      (localMorphism_isOpenImmersion D σ hA J p hover hOverlap hJ hcover
        (fun i => And.left (And.right (hres i))) i),?_,z,?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => k ≫ t) (Over.w (L i).hom)).trans hks)
  · change (L i).hom.left.base (k.base z) = x
    rw [hz]
    exact hy

/-- Exact trace of the WHOLE ORIGINAL singular inverse on every genuine source chart. -/
theorem local_preimage_intrinsicSingularLocus (i : D.J) :
    (L i).hom.left.base ⁻¹' ((F).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) =
      (p i).hom.left.base ⁻¹' intrinsicSingularLocus (B i).obj := by
  have hJR := preimage_intrinsicRegularLocus (J i).hom.left (hJ i) (Over.w (J i).hom)
  have hJS : (J i).hom.left.base ⁻¹' intrinsicSingularLocus X.obj =
      intrinsicSingularLocus (B i).obj := by
    simp only [intrinsicSingularLocus,preimage_compl,hJR]
  ext a
  change (F).hom.left.base ((L i).hom.left.base a) ∈ intrinsicSingularLocus X.obj ↔
    (p i).hom.left.base a ∈ intrinsicSingularLocus (B i).obj
  have hpt := congrArg (fun H => H.hom.left.base a)
    (localMorphism_projection D σ hA J p hover hOverlap hJ hcover (fun i => And.left (And.right (hres i))) i)
  change (F).hom.left.base ((L i).hom.left.base a) =
    (J i).hom.left.base ((p i).hom.left.base a) at hpt
  rw [hpt]
  exact Set.ext_iff.mp hJS ((p i).hom.left.base a)

variable (hreg : ∀ i, IsIsoOver (p i) (intrinsicRegularLocus (B i).obj))

include hreg in
/-- Full original-Reg protection descends using the DERIVED exact saturation. -/
theorem isIsoOver_intrinsicRegularLocus : IsIsoOver F (intrinsicRegularLocus X.obj) := by
  apply OriginalNativeIsoOverSaturatedCover.isIsoOver_of_saturated_cover F J L p hJ
    (fun i => localMorphism_isOpenImmersion D σ hA J p hover hOverlap hJ hcover
      (fun i => And.left (And.right (hres i))) i) hcover
    (fun i => localMorphism_projection D σ hA J p hover hOverlap hJ hcover
      (fun i => And.left (And.right (hres i))) i)
    (fun i => (preimage_chart_range D σ hA J p hover hOverlap i).symm)
    (intrinsicRegularLocus X.obj) (isOpen_intrinsicRegularLocus X.obj)
  intro i
  rw [preimage_intrinsicRegularLocus (J i).hom.left (hJ i) (Over.w (J i).hom)]
  exact hreg i

/-- Local bimeromorphic witnesses, not a supplied density packet, force global thinness. -/
theorem interior_preimage_intrinsicSingularLocus :
    interior ((F).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ := by
  apply OriginalAnalyticCover.interior_eq_empty_of_openImmersion_cover L
    (fun i => localMorphism_isOpenImmersion D σ hA J p hover hOverlap hJ hcover
      (fun i => And.left (And.right (hres i))) i)
    (localMorphism_cover D σ hA J p hover hOverlap hJ hcover (fun i => And.left (And.right (hres i))))
  intro i
  rw [local_preimage_intrinsicSingularLocus D σ hA J p hover hOverlap hJ hcover hres i]
  obtain ⟨_hp,E,_hEa,_hEt,hpre,hiso⟩ := (hres i).2
  exact hiso.interior_preimage_eq_empty hpre
    (OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty (B i))

theorem dense_preimage_intrinsicRegularLocus : Dense ((F).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  have h := interior_preimage_intrinsicSingularLocus D σ hA J p hover hOverlap hJ hcover hres
  rw [intrinsicSingularLocus,preimage_compl,interior_eq_empty_iff_dense_compl,compl_compl] at h
  exact h

include hreg in
/-- The SAME full projection is a resolution, with ORIGINAL Sing as its actual exceptional set. -/
theorem isResolution : IsResolution F := by
  refine ⟨source_isSmooth D σ hA J p hover hOverlap hJ hcover hres,
    projection_isProperMap D σ hA J p hover hOverlap hJ hcover (fun i => And.left (And.right (hres i))),
    intrinsicSingularLocus X.obj,
    OriginalIntrinsicSingularLocus.isAnalyticSubset_intrinsicSingularLocus X,
    OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty X,
    interior_preimage_intrinsicSingularLocus D σ hA J p hover hOverlap hJ hcover hres,?_⟩
  simpa only [intrinsicSingularLocus,compl_compl] using
    isIsoOver_intrinsicRegularLocus D σ hA J p hover hOverlap hJ hcover hres hreg

include hreg in
theorem surjective : Function.Surjective (F).hom.left.base :=
  (isResolution D σ hA J p hover hOverlap hJ hcover hres hreg).2.surjective

end
end Hironaka.Analytic.Unibranch.OriginalNativeResolutionAtlas
