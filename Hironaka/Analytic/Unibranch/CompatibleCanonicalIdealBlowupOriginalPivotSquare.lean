import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotObjects

/-! Actual ORIGINAL restricted canonical morphisms on SAME literal pivot opens.
Complete blueprint FIRST; ordinary643 ONCE then A/699 model helpers SAME E.
Derived range retains V. No incoming range/square/property/Iso packet.
Unit B only: C ambient comparison, .7, Qsat and raw-fibre remain open. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotSquare
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupStrictSubmanifold
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace EmbeddedGeometricBlowup OriginalFiniteIdealGraphChart
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotOpenRanges CompatibleCanonicalIdealBlowupPivotOpenRestrictions
  CompatibleCanonicalIdealBlowupOriginalPivotObjects
open scoped ProductComplexManifold

noncomputable section
section SameCanonical
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b
variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)

-- This range inclusion is DERIVED from699 exact PX=V-intersect-preimage,
-- not a public ordinary caller input. Native inclusion OI instances are direct
-- typed specializations of336 literalOpenInclusion_isOpenImmersion.
instance targetPivotInclusion_isOpenImmersion (j : Fin t.rank) :
  LocallyRingedSpace.IsOpenImmersion (targetPivotInclusion B b F x t c g d E j) := by
  change LocallyRingedSpace.IsOpenImmersion
    ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.ofRestrict
      (targetPivotOpen B b F x t c g d E j).isOpenEmbedding)
  exact LocallyRingedSpace.IsOpenImmersion.ofRestrict _ _

instance sourcePivotInclusion_isOpenImmersion (j : Fin t.rank) :
  LocallyRingedSpace.IsOpenImmersion (sourcePivotInclusion B b F x t c g d E j) := by
  change LocallyRingedSpace.IsOpenImmersion
    ((OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left.ofRestrict
      (sourcePivotOpen B b F x t c g d E j).isOpenEmbedding)
  exact LocallyRingedSpace.IsOpenImmersion.ofRestrict _ _

theorem native_pivot_map_range (j : Fin t.rank) :
  Set.range ((sourcePivotInclusion B b F x t c g d E j) ≫
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left).base ⊆
      Set.range (targetPivotInclusion B b F x t c g d E j).base := by
  obtain ⟨P⟩ := pivot_open_ranges_of_models B b F x t c g d E
  rintro q ⟨z,rfl⟩
  have hz : z.val ∈ (sourcePivotOpen B b F x t c g d E j).1 := z.property
  rw [P.source_preimage j] at hz
  exact ⟨⟨(OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z.val,
    hz.2⟩,rfl⟩

def nativePivotMap (j : Fin t.rank) :
    sourcePivotRestriction B b F x t c g d E j ⟶
      targetPivotRestriction B b F x t c g d E j :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (targetPivotInclusion B b F x t c g d E j)
    (sourcePivotInclusion B b F x t c g d E j ≫
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left)
    (native_pivot_map_range B b F x t c g d E j)

theorem native_pivot_map_fac (j : Fin t.rank) :
  nativePivotMap B b F x t c g d E j ≫ targetPivotInclusion B b F x t c g d E j =
    sourcePivotInclusion B b F x t c g d E j ≫
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left := by
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

theorem native_pivot_map_point (j : Fin t.rank) :
  nativePivotMap B b F x t c g d E j ≫
      (targetPivotInclusion B b F x t c g d E j ≫
        (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom) =
    sourcePivotInclusion B b F x t c g d E j ≫
      (OriginalFiniteIdealGeometricBlowup.sourceObject
        (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.hom := by
  rw [← Category.assoc,native_pivot_map_fac,Category.assoc]
  exact congrArg (fun k => sourcePivotInclusion B b F x t c g d E j ≫ k)
    (Over.w (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom)

-- UnitA proof data O changes NO native space, structural map or chart choice.
-- The actual full map below is the existing native lift, bundled via its
-- derived genuine scalar law, never assembled from point values.
def originalPivotMap (O : OriginalPivotObjectData B b F x t c g d E)
    (j : Fin t.rank) :
    sourceOriginalPivot B b F x t c g d E O.properties j ⟶
      targetOriginalPivot B b F x t c g d E O.properties j :=
  ObjectProperty.homMk (Over.homMk
    (nativePivotMap B b F x t c g d E j)
    (native_pivot_map_point B b F x t c g d E j))

structure OriginalPivotSquareData where
  objects : OriginalPivotObjectData B b F x t c g d E
  restricted_map : ∀ j : Fin t.rank,
    sourceOriginalPivot B b F x t c g d E objects.properties j ⟶
      targetOriginalPivot B b F x t c g d E objects.properties j
  restricted_native : ∀ j : Fin t.rank,
    (restricted_map j).hom.left = nativePivotMap B b F x t c g d E j
  canonical_square : ∀ j : Fin t.rank,
    restricted_map j ≫ targetOriginalInclusion B b F x t c g d E objects.properties j =
      sourceOriginalInclusion B b F x t c g d E objects.properties j ≫
        OriginalFiniteIdealBlowupSquare.inducedMorphism B b F
  projection_square : ∀ j : Fin t.rank,
    restricted_map j ≫ targetOriginalInclusion B b F x t c g d E objects.properties j ≫
        OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      sourceOriginalInclusion B b F x t c g d E objects.properties j ≫
        OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b) ≫ F
  genuine_scalar : ∀ j : Fin t.rank,
    (restricted_map j).hom.left ≫
        (targetOriginalPivot B b F x t c g d E objects.properties j).obj.hom =
      (sourceOriginalPivot B b F x t c g d E objects.properties j).obj.hom
  unique : ∀ (j : Fin t.rank)
    (L : sourceOriginalPivot B b F x t c g d E objects.properties j ⟶
      targetOriginalPivot B b F x t c g d E objects.properties j),
    L ≫ targetOriginalInclusion B b F x t c g d E objects.properties j =
        sourceOriginalInclusion B b F x t c g d E objects.properties j ≫
          OriginalFiniteIdealBlowupSquare.inducedMorphism B b F → L = restricted_map j
  target_projection : ∀ j : Fin t.rank,
    (objects.target_iso j).hom ≫ targetOriginalInclusion B b F x t c g d E objects.properties j ≫
        OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      targetStrictInclusion B b F x t c g d E j ≫
        geometricProjectionMorphism
          (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic ≫
        chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic
  source_projection : ∀ j : Fin t.rank,
    (objects.source_iso j).hom ≫ sourceOriginalInclusion B b F x t c g d E objects.properties j ≫
        OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b) =
      sourceStrictInclusion B b F x t c g d E j ≫
        geometricProjectionMorphism
          (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic ≫ c.chart

theorem original_pivot_square_of_models :
  Nonempty (OriginalPivotSquareData B b F x t c g d E) := by
  obtain ⟨O⟩ := original_pivot_objects_of_models B b F x t c g d E
  have hcan (j : Fin t.rank) :
      originalPivotMap B b F x t c g d E O j ≫
          targetOriginalInclusion B b F x t c g d E O.properties j =
        sourceOriginalInclusion B b F x t c g d E O.properties j ≫
          OriginalFiniteIdealBlowupSquare.inducedMorphism B b F := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact native_pivot_map_fac B b F x t c g d E j
  have hproj (j : Fin t.rank) :
      originalPivotMap B b F x t c g d E O j ≫
          targetOriginalInclusion B b F x t c g d E O.properties j ≫
            OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
        sourceOriginalInclusion B b F x t c g d E O.properties j ≫
          OriginalFiniteIdealGeometricBlowup.projectionMorphism
            (nativePulledIdealModule F.hom.left B b)
            (nativePulledIdealInclusion F.hom.left B b) ≫ F := by
    rw [← Category.assoc,hcan,Category.assoc,
      OriginalFiniteIdealBlowupSquare.inducedMorphism_square]
  have huniq (j : Fin t.rank)
      (L : sourceOriginalPivot B b F x t c g d E O.properties j ⟶
        targetOriginalPivot B b F x t c g d E O.properties j)
      (hL : L ≫ targetOriginalInclusion B b F x t c g d E O.properties j =
        sourceOriginalInclusion B b F x t c g d E O.properties j ≫
          OriginalFiniteIdealBlowupSquare.inducedMorphism B b F) :
      L = originalPivotMap B b F x t c g d E O j := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (targetPivotInclusion B b F x t c g d E j)).mp
    exact (congrArg (fun k => k.hom.left) hL).trans
      (native_pivot_map_fac B b F x t c g d E j).symm
  have ht (j : Fin t.rank) :
      (O.target_iso j).hom ≫ targetOriginalInclusion B b F x t c g d E O.properties j ≫
          OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
        targetStrictInclusion B b F x t c g d E j ≫
          geometricProjectionMorphism
            (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic ≫
          chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic := by
    rw [← Category.assoc,target_original_iso_inclusion,Category.assoc,E.target_maps.projection]
  have hs (j : Fin t.rank) :
      (O.source_iso j).hom ≫ sourceOriginalInclusion B b F x t c g d E O.properties j ≫
          OriginalFiniteIdealGeometricBlowup.projectionMorphism
            (nativePulledIdealModule F.hom.left B b)
            (nativePulledIdealInclusion F.hom.left B b) =
        sourceStrictInclusion B b F x t c g d E j ≫
          geometricProjectionMorphism
            (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic ≫ c.chart := by
    rw [← Category.assoc,source_original_iso_inclusion,Category.assoc,E.source_maps.projection]
  exact ⟨{
    objects := O
    restricted_map := originalPivotMap B b F x t c g d E O
    restricted_native := fun _ => rfl
    canonical_square := hcan
    projection_square := hproj
    genuine_scalar := fun j => Over.w (originalPivotMap B b F x t c g d E O j).hom
    unique := huniq
    target_projection := ht
    source_projection := hs }⟩
end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

theorem exists_same_canonical_original_pivot_square
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y)
      (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c)
      (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d)
      (_M : AllAmbientMonomialLiftData B b F x t c g d E),
      Nonempty (OriginalPivotSquareData B b F x t c g d E) := by
  obtain ⟨t,c,g,d,E,⟨M⟩⟩ := exists_same_canonical_allambient_monomial_lift B b F x y hxy
  exact ⟨t,c,g,d,E,M,original_pivot_square_of_models B b F x t c g d E⟩

end OrdinaryCaller
end

end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotSquare
