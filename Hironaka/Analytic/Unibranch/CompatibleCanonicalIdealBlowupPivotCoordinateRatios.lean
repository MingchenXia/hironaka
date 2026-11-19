import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotMonomialConjugacy
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupProductNormalFactors

/-!
Original normal functions retain the exceptional factor in the SAME pivot
charts.  The native strict quotient and actual canonical section dictionaries
are retained.  The exact original restricted map preserves the normal chart
slots and their query-point offsets.  No cancellation, raw-pair source point,
overlap, saturation, raw-fibre or global flattening conclusion is asserted.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotCoordinateRatios
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualWholeStalkHolomorphicPullback
  HironakaFiniteSectionProductGraph
  SourceReducedComplexSpace EmbeddedGeometricBlowup OriginalFiniteIdealGraphChart
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotChart CompatibleCanonicalIdealBlowupPivotOpenRanges
  CompatibleCanonicalIdealBlowupOriginalPivotObjects
  CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  CompatibleCanonicalIdealBlowupPivotMonomialConjugacy
  CompatibleCanonicalIdealBlowupProductNormalFactors
open scoped ProductComplexManifold

private theorem actual_product_domain_mem {n r : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    (a : ProductNormalCharts n r P) (j : Fin r) (q : P × ComplexModel r) :
    q ∈ (productNormalChart (n := n) a.base j).dom := by
  rw [a.domain j]
  trivial

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

theorem target_original_section_factor (j i : Fin t.rank)
    (z : strictChartCarrier E.target.charts (targetGraphSet B b t) j) :
    (targetChartMap B b F x t c g d E j).stalkMap z
        (targetSectionGerm B b F x t c g d E j i z) =
      strictNormalClass E.target.charts (targetGraphSet B b t) j j z *
        (if i=j then 1 else strictNormalClass E.target.charts (targetGraphSet B b t) j i z) := by
  exact strict_section_original_normal_factor E.target.charts (targetGraphSet B b t)
    ((targetCanonicalMap B b t E.target).hom.left) j i z
    (targetSectionGerm B b F x t c g d E j i z)
    (E.target_normals.normal ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z) j i)

private theorem source_parent_normal_dictionary (j i : Fin t.rank)
    (z : strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j) :
    (sourceChartMap B b F x t c g d E j).stalkMap z
        (sourceSectionGerm B b F x t c g d E j i z) =
      (strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).stalkMap z
        (sourceCoordinateClass B b F x t c g d E j i z) := by
  have hP : Nonempty (PivotChartRangeData B b F x t c g d E) :=
    pivot_chart_ranges_of_models B b F x t c g d E
  obtain ⟨P⟩ := hP
  exact P.source_normals.normal j i z

private theorem source_coordinate_class_def (j i : Fin t.rank)
    (z : strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j) :
    sourceCoordinateClass B b F x t c g d E j i z =
      geometricCoordinateClass (sourceGraphSet B b F x t c)
        (productNormalChart (n := c.embedding.dim) E.source.charts.base j)
        ((strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).base z)
        (actual_product_domain_mem E.source.charts j _) (i.natAdd c.embedding.dim) := by
  rfl

theorem source_original_section_factor (j i : Fin t.rank)
    (z : strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j) :
    (sourceChartMap B b F x t c g d E j).stalkMap z
        (sourceSectionGerm B b F x t c g d E j i z) =
      strictNormalClass E.source.charts (sourceGraphSet B b F x t c) j j z *
        (if i=j then 1 else strictNormalClass E.source.charts (sourceGraphSet B b F x t c) j i z) := by
  have hc := congrArg
    ((strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).stalkMap z)
    (source_coordinate_class_def B b F x t c g d E j i z)
  exact (source_parent_normal_dictionary B b F x t c g d E j i z).trans
    (hc.trans (strict_original_normal_factor E.source.charts (sourceGraphSet B b F x t c) j i z))

variable (M : AllAmbientMonomialLiftData B b F x t c g d E)

include M in
private theorem monomial_normal_coordinate (j i : Fin t.rank)
    (z : productChartOpen E.source.charts j) :
    productNormalFunction E.target.charts j i
        (monomialAmbientFunction B b F x t c g d E j z) =
      productNormalFunction E.source.charts j i z := by
  have hs := congrArg (fun k => k.base z) (M.chart_square j)
  have hn := M.normal_slots j i (productChartDiffeomorph E.source.charts j z)
  exact (congrArg (fun w => w.val (i.natAdd t.embedding.dim)) hs).trans hn

variable (C : PivotMonomialConjugacyData B b F x t c g d E M)

def targetPivotNormalCoordinate (j i : Fin t.rank)
    (q : (targetOriginalPivot B b F x t c g d E C.canonical.objects.properties j).obj.left) : ℂ :=
  productNormalFunction E.target.charts j i
    ((C.canonical.objects.target_iso j).inv.hom.left.base q).val

def sourcePivotNormalCoordinate (j i : Fin t.rank)
    (q : (sourceOriginalPivot B b F x t c g d E C.canonical.objects.properties j).obj.left) : ℂ :=
  productNormalFunction E.source.charts j i
    ((C.canonical.objects.source_iso j).inv.hom.left.base q).val

theorem original_pivot_normal_coordinate (j i : Fin t.rank)
    (q : (sourceOriginalPivot B b F x t c g d E C.canonical.objects.properties j).obj.left) :
    targetPivotNormalCoordinate B b F x t c g d E M C j i
        ((C.canonical.restricted_map j).hom.left.base q) =
      sourcePivotNormalCoordinate B b F x t c g d E M C j i q := by
  have h := congrArg (fun k => k.hom.left.base q) (C.inverse j)
  change (C.canonical.objects.target_iso j).inv.hom.left.base
      ((C.canonical.restricted_map j).hom.left.base q) =
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left.base
      ((C.canonical.objects.source_iso j).inv.hom.left.base q) at h
  unfold targetPivotNormalCoordinate sourcePivotNormalCoordinate
  rw [h]
  exact monomial_normal_coordinate B b F x t c g d E M j i _

theorem original_pivot_normal_coordinate_offset (j i : Fin t.rank)
    (q q₀ : (sourceOriginalPivot B b F x t c g d E C.canonical.objects.properties j).obj.left) :
    targetPivotNormalCoordinate B b F x t c g d E M C j i
        ((C.canonical.restricted_map j).hom.left.base q) -
      targetPivotNormalCoordinate B b F x t c g d E M C j i
        ((C.canonical.restricted_map j).hom.left.base q₀) =
      sourcePivotNormalCoordinate B b F x t c g d E M C j i q -
        sourcePivotNormalCoordinate B b F x t c g d E M C j i q₀ := by
  rw [original_pivot_normal_coordinate,original_pivot_normal_coordinate]

/-- Named output assertions only. These do not introduce new coordinates,
sections, stalk actions or mathematical engines. -/
structure PivotCoordinateRatioLaws : Prop where
  target_factor : ∀ (j i : Fin t.rank)
    (z : strictChartCarrier E.target.charts (targetGraphSet B b t) j),
    (targetChartMap B b F x t c g d E j).stalkMap z
        (targetSectionGerm B b F x t c g d E j i z) =
      strictNormalClass E.target.charts (targetGraphSet B b t) j j z *
        (if i=j then 1 else strictNormalClass E.target.charts (targetGraphSet B b t) j i z)
  source_factor : ∀ (j i : Fin t.rank)
    (z : strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j),
    (sourceChartMap B b F x t c g d E j).stalkMap z
        (sourceSectionGerm B b F x t c g d E j i z) =
      strictNormalClass E.source.charts (sourceGraphSet B b F x t c) j j z *
        (if i=j then 1 else strictNormalClass E.source.charts (sourceGraphSet B b F x t c) j i z)
  coordinate : ∀ (j i : Fin t.rank)
    (q : (sourceOriginalPivot B b F x t c g d E C.canonical.objects.properties j).obj.left),
    targetPivotNormalCoordinate B b F x t c g d E M C j i
        ((C.canonical.restricted_map j).hom.left.base q) =
      sourcePivotNormalCoordinate B b F x t c g d E M C j i q
  offset : ∀ (j i : Fin t.rank)
    (q q₀ : (sourceOriginalPivot B b F x t c g d E C.canonical.objects.properties j).obj.left),
    targetPivotNormalCoordinate B b F x t c g d E M C j i
        ((C.canonical.restricted_map j).hom.left.base q) -
      targetPivotNormalCoordinate B b F x t c g d E M C j i
        ((C.canonical.restricted_map j).hom.left.base q₀) =
      sourcePivotNormalCoordinate B b F x t c g d E M C j i q -
        sourcePivotNormalCoordinate B b F x t c g d E M C j i q₀

theorem pivot_coordinate_ratio_laws_of_models :
    PivotCoordinateRatioLaws B b F x t c g d E M C where
  target_factor := target_original_section_factor B b F x t c g d E
  source_factor := source_original_section_factor B b F x t c g d E
  coordinate := original_pivot_normal_coordinate B b F x t c g d E M C
  offset := original_pivot_normal_coordinate_offset B b F x t c g d E M C

end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

/-- One choice from ordinary original inputs before every label, point and
germ. No input model, conjugacy, ratio or original-section equation. -/
theorem exists_same_canonical_pivot_coordinate_ratios
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y)
      (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c)
      (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d)
      (M : AllAmbientMonomialLiftData B b F x t c g d E)
      (C : PivotMonomialConjugacyData B b F x t c g d E M),
      PivotCoordinateRatioLaws B b F x t c g d E M C := by
  obtain ⟨t,c,g,d,E,M,⟨C⟩⟩ := exists_same_canonical_pivot_monomial_conjugacy B b F x y hxy
  exact ⟨t,c,g,d,E,M,C,pivot_coordinate_ratio_laws_of_models B b F x t c g d E M C⟩
end OrdinaryCaller
end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotCoordinateRatios
