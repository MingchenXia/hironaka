import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupObjectGluing
import Hironaka.Analytic.Unibranch.EmbeddedBlowupTopology
import Hironaka.Analytic.Unibranch.EmbeddedBlowupParacompact

/-!
# The same whole-ideal glued blowup in the original category

The actual local strict transforms and their derived saturated homeomorphisms
give global Hausdorffness, local compactness and properness by the existing
generic topology theorem. Properness over the original paracompact base then
gives source paracompactness. The exact actual analytic atlas completes the
original category object on the same native LRS and full projection.
No centre containment, reduced target ideal or global countability is used.
Blueprint: `embedded-ideal-blowup-original-object.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalObject

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace EmbeddedBlowup

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
  (hd : ∀ i, W i ⊆ closure (W i \ C i))
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
    EmbeddedIdealBlowupObjectGluing.localObject hW hπ i → chartOpen hW J i :=
  chartRangeHomeomorph hW J i ∘ (strictTransformProjection (hπ i) (hW i).isClosed).base

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
    T2Space (EmbeddedIdealBlowupObjectGluing.glued hW hπ J B b hd hJ) ∧
    LocallyCompactSpace (EmbeddedIdealBlowupObjectGluing.glued hW hπ J B b hd hJ) ∧
    IsProperMap (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base := by
  refine @EmbeddedBlowupTopology.topology_of_local_models X.obj.left
    (EmbeddedIdealBlowupObjectGluing.glued hW hπ J B b hd hJ) ι _ _ X.property.1
    (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base
    (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base.hom.continuous
    (chartOpen hW J) (chartOpen_cover hW J hcover)
    (fun i => (EmbeddedIdealBlowupObjectGluing.localObject hW hπ i : Type))
    (fun i => inferInstance)
    (EmbeddedIdealBlowupObjectGluing.saturatedHomeomorph hW hπ J B b hd hJ)
    (localTargetProjection hW hπ J) ?_ ?_ ?_ ?_
  · intro i
    funext x
    apply Subtype.ext
    exact EmbeddedIdealBlowupObjectGluing.saturatedHomeomorph_projection hW hπ J B b hd hJ i x
  · intro i
    exact (chartRangeHomeomorph hW J i).isProperMap.comp
      (strictTransformProjection_isProperMap (hπ i) (hW i).isClosed)
  · intro i
    change T2Space (strictTransform (n i) (π i) (W i))
    infer_instance
  · intro i
    let : LocallyCompactSpace (Y i) := ChartedSpace.locallyCompactSpace (ComplexModel (n i)) (Y i)
    change LocallyCompactSpace (strictTransform (n i) (π i) (W i))
    exact isClosed_closure.locallyCompactSpace

/-- Original base paracompactness and derived properness suffice; no global SC. -/
theorem glued_paracompact :
    ParacompactSpace (EmbeddedIdealBlowupObjectGluing.glued hW hπ J B b hd hJ) := by
  exact @EmbeddedBlowupParacompact.paracompactSpace_of_isProperMap X.obj.left
    (EmbeddedIdealBlowupObjectGluing.glued hW hπ J B b hd hJ) _ _ X.property.2.1
    (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base
    (glued_topology hW hπ J B b hd hJ hcover).2.2

/-- The SAME native LRS and actual scalar map in the EXISTING original category. -/
@[implicit_reducible]
def sourceObject : SourceReducedComplexSpace := by
  refine ⟨Over.mk (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ ≫ X.obj.hom),
    (glued_topology hW hπ J B b hd hJ hcover).1,
    glued_paracompact hW hπ J B b hd hJ hcover, ?_⟩
  exact EmbeddedIdealBlowupObjectGluing.original_analytic_atlas hW hπ J B b hd hJ

/-- The literal same full projection as an ORIGINAL morphism. -/
def projectionMorphism : sourceObject hW hπ J B b hd hJ hcover ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ) rfl)

/-- Each SAME local strict-transform inclusion in the original category. -/
def localMorphism (i : ι) : EmbeddedIdealBlowupOverlap.localSpace hW hπ i ⟶
    sourceObject hW hπ J B b hd hJ hcover := by
  apply ObjectProperty.homMk
  refine Over.homMk (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i) ?_
  change EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i ≫
    (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ ≫ X.obj.hom) = _
  rw [← Category.assoc, EmbeddedIdealBlowupObjectGluing.inclusion_projection,
    EmbeddedIdealBlowupObjectGluing.localProjection_point]
  rfl

instance localMorphism_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (localMorphism hW hπ J B b hd hJ hcover i).hom.left :=
  EmbeddedIdealBlowupObjectGluing.inclusion_isOpenImmersion hW hπ J B b hd hJ i

/-- The ENTIRE original projection square, retaining the original chart J. -/
theorem localMorphism_projection (i : ι) :
    localMorphism hW hπ J B b hd hJ hcover i ≫
      projectionMorphism hW hπ J B b hd hJ hcover =
        strictTransformMorphism (hπ i) (hW i) ≫ J i := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact EmbeddedIdealBlowupObjectGluing.inclusion_projection hW hπ J B b hd hJ i

theorem projection_isProperMap :
    IsProperMap (projectionMorphism hW hπ J B b hd hJ hcover).hom.left.base :=
  (glued_topology hW hπ J B b hd hJ hcover).2.2

theorem projection_surjective :
    Function.Surjective (projectionMorphism hW hπ J B b hd hJ hcover).hom.left.base :=
  EmbeddedIdealBlowupObjectGluing.projection_surjective hW hπ J B b hd hJ hcover

/-- Compactness is derived only when the ORIGINAL base is compact. -/
theorem sourceObject_compact [CompactSpace X.obj.left] :
    CompactSpace (sourceObject hW hπ J B b hd hJ hcover).obj.left := by
  have hXcompact : IsCompact (univ : Set X.obj.left) := isCompact_univ
  constructor
  simpa only [preimage_univ] using
    (projection_isProperMap hW hπ J B b hd hJ hcover).isCompact_preimage hXcompact

end

end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalObject
