import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalCoverage
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover

/-!
# H3.4 (chart choice): a target pivot chart point with zero pivot coordinate

Lane G10H3, run 0081.  Setting of `HironakaG10SbCanonicalStrictTorsion` (canonical chart data `t c g d E` at a source
point `x` and a target point `y` of `Bl_B Y`).

* `exists_target_pivot_point` — if `y` lies over the centre, it is `targetChartMap j p` for a pivot `j` and a target
  strict chart point `p` with zero pivot coordinate (the input of G10FI's `HironakaG10NfFibreCover.exists_origin`).

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfChartChoice

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotChart
  Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalCoverage

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

/-- **A target point over the centre is a target pivot chart point with zero pivot coordinate.** -/
theorem exists_target_pivot_point
    (hc : (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y ∈
      EmbeddedIdealBlowupNonunitLocus.nonunitLocus B b) :
    ∃ (j : Fin t.rank) (p : strictChartCarrier E.target.charts (targetGraphSet B b t) j),
      (targetChartMap B b F x t c g d E j).base p = y ∧
        productChartCoordinates E.target.charts j p.val (j.natAdd t.embedding.dim) = 0 := by
  have hcent : nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
      B b y ≠ ⊤ := fun htop =>
    hc ((OriginalFiniteIdealGraphDensity.nativePulledIdealStalkIdeal_eq_top_iff
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b y).mp htop)
  have hP := pivot_open_ranges_of_models B b F x t c g d E
  refine hP.elim fun P => ?_
  have h1 : y ∈ (⋃ j : Fin t.rank, (targetPivotOpen B b F x t c g d E j).1) :=
    Eq.mpr (congrArg (fun A => y ∈ A) P.target_cover) d.target.target_mem
  refine (Set.mem_iUnion.mp h1).elim fun j hj => ?_
  have hj' : y ∈ range (targetChartMap B b F x t c g d E j).base :=
    Eq.mpr (congrArg (fun A => y ∈ A) (P.chart_ranges.target_range j)) hj
  refine (Set.mem_range.mp hj').elim fun p hp => ?_
  have hcent' : nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
      B b ((targetChartMap B b F x t c g d E j).base p) ≠ ⊤ :=
    (congrArg (fun z => nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
      B b z ≠ ⊤) hp).mpr hcent
  have hwh := E.target_normals.whole_ideal
    ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base p)
  have hne : strictCentreStalkIdeal (targetGraphSet B b t)
      ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base p) ≠ ⊤ := fun htop =>
    @map_ne_top_of_ne_top _ _ _ _ (LocallyRingedSpace.isLocalRing _ _)
      ((explicitTarget B b t).obj.left.isLocalRing _) _
      (LocallyRingedSpace.isLocalHomStalkMap (targetCanonicalMap B b t E.target).hom.left _) _ hcent'
      (hwh.trans htop)
  exact ⟨j, p, hp, pivot_coordinate_eq_zero_of_ne_top E.target.charts t.positive (targetGraphSet B b t)
    t.analytic.isClosed j p hne⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10NfChartChoice
