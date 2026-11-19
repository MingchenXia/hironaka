import Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealObjectGluing
import Hironaka.Analytic.Unibranch.EmbeddedBlowupTopology
import Hironaka.Analytic.Unibranch.EmbeddedBlowupParacompact
import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup

/-!
# The SAME geometric whole-ideal blowup in the original category, without density

The actual local geometric transforms and their derived saturated homeomorphisms
give global Hausdorffness, local compactness and properness by the existing
generic topology theorem. Properness over the original paracompact base then
gives source paracompactness. The exact actual analytic atlas completes the
original category object on the same native LRS and full projection.
No target density, source-projection surjectivity, centre containment, reduced target ideal or global countability is used. Generic topology/category reuse has zero separate geometric credit.
Blueprint: `embedded-geometric-ideal-original-object.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOriginalObject

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace EmbeddedGeometricBlowup BlowupStrictSubmanifold

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ}
  {M Y : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (HironakaSmoothCentreRealDomainActualSheafStalk.actualWholeSheafStalkIdeal
        (HolomorphicIdealSheaves.vanishingIdeal (n := n i) (C i)) y.val) =
          nativePulledIdealStalkIdeal (J i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

private def chartOpen (i : ι) : Opens X.obj.left :=
  ⟨range (J i).hom.left.base, (hJopen i).base_open.isOpen_range⟩

private def chartRangeHomeomorph (i : ι) : W i ≃ₜ chartOpen hW J i :=
  (hJopen i).base_open.isEmbedding.toHomeomorph

private def localTargetProjection (i : ι) :
    EmbeddedGeometricIdealObjectGluing.localObject hW hπ i → chartOpen hW J i :=
  chartRangeHomeomorph hW J i ∘ (geometricProjection (hπ i) (hW i).isClosed).base

include hcover in
private theorem chartOpen_cover : IsOpenCover (chartOpen hW J) := by
  apply IsOpenCover.of_sets (fun i => (hJopen i).base_open.isOpen_range)
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i, w, hw⟩ := hcover x
  exact ⟨i, w, hw⟩

include hcover

/-- Existing generic topology on the SAME actual native glued source. -/
theorem glued_topology :
    T2Space (EmbeddedGeometricIdealObjectGluing.glued hW hπ J B b hJ) ∧
    LocallyCompactSpace (EmbeddedGeometricIdealObjectGluing.glued hW hπ J B b hJ) ∧
    IsProperMap (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ).base := by
  refine @EmbeddedBlowupTopology.topology_of_local_models X.obj.left
    (EmbeddedGeometricIdealObjectGluing.glued hW hπ J B b hJ) ι _ _ X.property.1
    (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ).base
    (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ).base.hom.continuous
    (chartOpen hW J) (chartOpen_cover hW J hcover)
    (fun i => (EmbeddedGeometricIdealObjectGluing.localObject hW hπ i : Type))
    (fun i => inferInstance)
    (EmbeddedGeometricIdealObjectGluing.saturatedHomeomorph hW hπ J B b hJ)
    (localTargetProjection hW hπ J) ?_ ?_ ?_ ?_
  · intro i
    funext x
    apply Subtype.ext
    exact EmbeddedGeometricIdealObjectGluing.saturatedHomeomorph_projection hW hπ J B b hJ i x
  · intro i
    exact (chartRangeHomeomorph hW J i).isProperMap.comp
      (geometricProjection_isProperMap (hπ i) (hW i).isClosed)
  · intro i
    change T2Space (geoStrictTransform (π i) (C i) (W i))
    infer_instance
  · intro i
    let : LocallyCompactSpace (Y i) := ChartedSpace.locallyCompactSpace (ComplexModel (n i)) (Y i)
    change LocallyCompactSpace (geoStrictTransform (π i) (C i) (W i))
    exact isClosed_closure.locallyCompactSpace

/-- Original base paracompactness and derived properness suffice; no global SC. -/
theorem glued_paracompact :
    ParacompactSpace (EmbeddedGeometricIdealObjectGluing.glued hW hπ J B b hJ) := by
  exact @EmbeddedBlowupParacompact.paracompactSpace_of_isProperMap X.obj.left
    (EmbeddedGeometricIdealObjectGluing.glued hW hπ J B b hJ) _ _ X.property.2.1
    (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ).base
    (glued_topology hW hπ J B b hJ hcover).2.2

/-- The SAME native LRS and actual scalar map in the EXISTING original category. -/
@[implicit_reducible]
def sourceObject : SourceReducedComplexSpace := by
  refine ⟨Over.mk (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ ≫ X.obj.hom),
    (glued_topology hW hπ J B b hJ hcover).1,
    glued_paracompact hW hπ J B b hJ hcover, ?_⟩
  exact EmbeddedGeometricIdealObjectGluing.original_analytic_atlas hW hπ J B b hJ

/-- The literal same full projection as an ORIGINAL morphism. -/
def projectionMorphism : sourceObject hW hπ J B b hJ hcover ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ) rfl)

/-- Each SAME local geometric-transform inclusion in the original category. -/
def localMorphism (i : ι) : EmbeddedGeometricIdealOverlap.localSpace hW hπ i ⟶
    sourceObject hW hπ J B b hJ hcover := by
  apply ObjectProperty.homMk
  refine Over.homMk (EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i) ?_
  change EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i ≫
    (EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ ≫ X.obj.hom) = _
  rw [← Category.assoc, EmbeddedGeometricIdealObjectGluing.inclusion_projection,
    EmbeddedGeometricIdealObjectGluing.localProjection_point]
  rfl

instance localMorphism_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (localMorphism hW hπ J B b hJ hcover i).hom.left :=
  EmbeddedGeometricIdealObjectGluing.inclusion_isOpenImmersion hW hπ J B b hJ i

/-- The ENTIRE original projection square, retaining the original chart J. -/
theorem localMorphism_projection (i : ι) :
    localMorphism hW hπ J B b hJ hcover i ≫
      projectionMorphism hW hπ J B b hJ hcover =
        geometricProjectionMorphism (hπ i) (hW i) ≫ J i := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact EmbeddedGeometricIdealObjectGluing.inclusion_projection hW hπ J B b hJ i

theorem projection_isProperMap :
    IsProperMap (projectionMorphism hW hπ J B b hJ hcover).hom.left.base :=
  (glued_topology hW hπ J B b hJ hcover).2.2

/-- Compactness is derived only when the ORIGINAL base is compact. -/
theorem sourceObject_compact [CompactSpace X.obj.left] :
    CompactSpace (sourceObject hW hπ J B b hJ hcover).obj.left := by
  have hXcompact : IsCompact (univ : Set X.obj.left) := isCompact_univ
  constructor
  simpa only [preimage_univ] using
    (projection_isProperMap hW hπ J B b hJ hcover).isCompact_preimage hXcompact

end

end Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOriginalObject
