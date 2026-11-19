import Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation

/-! The recentered origin is the actual original exceptional chart point. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin
noncomputable section
open Hironaka Hironaka
  HironakaRealOpenGeometricStrictSaturation HironakaG10ArbitraryBaseRecenter
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]
variable (a : ProductNormalCharts n r P) (j : Fin r)

/-- Recentring at an actual exceptional point sends zero back to that same point. -/
theorem arbitrary_canonical_origin_eq (z : productChartOpen a j)
    (hvj : productChartCoordinates a j z (j.natAdd n) = 0)
    (h0 : (0 : ComplexModel (n+r)) ∈ recenteredTargetOpen n r j
      (productChartCoordinates a j z) (canonicalTargetOpen a j)) :
    arbitraryCanonicalRecenteredChart a j (productChartCoordinates a j z) hvj
      (realOpenOrigin n r j (fun i => productChartCoordinates a j z i)
        (recenteredTargetOpen n r j (productChartCoordinates a j z) (canonicalTargetOpen a j)) h0) = z := by
  apply (productChartDiffeomorph a j).injective
  apply Subtype.ext
  change productChartCoordinates a j
    (arbitraryCanonicalRecenteredChart a j (productChartCoordinates a j z) hvj
      (realOpenOrigin n r j (fun i => productChartCoordinates a j z i)
        (recenteredTargetOpen n r j (productChartCoordinates a j z) (canonicalTargetOpen a j)) h0)) =
      productChartCoordinates a j z
  rw [arbitrary_canonical_recentered_coordinates]
  simp [realOpenOrigin]

open CategoryTheory Opposite AlgebraicGeometry
open Hironaka.HolomorphicIdealSheaves
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaG10RealOpenStrictTorsionKernel
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)

/-- The canonical saturation neighbourhood contains the recentering of the
actual exceptional chart point, and the chart sends it back to that point. -/
theorem actual_exceptional_point_in_saturation_domain
    (j : Fin t.rank) (z : productChartOpen E.source.charts j)
    (hvj : productChartCoordinates E.source.charts j z (j.natAdd c.embedding.dim) = 0) :
    let v := productChartCoordinates E.source.charts j z
    let h0 := canonical_target_origin B b F x t c g d E j z
    ∃ w : sourceDomain B b F x t c g d E j v,
      arbitraryCanonicalRecenteredChart E.source.charts j v hvj w = z ∧
      w ∈ localDomain c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
          (originalGraph_analytic B b F x t c g d E j v) := by
  let v := productChartCoordinates E.source.charts j z
  let h0 := canonical_target_origin B b F x t c g d E j z
  let w := realOpenOrigin c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) h0
  refine ⟨w, arbitrary_canonical_origin_eq E.source.charts j z hvj h0, ?_⟩
  exact origin_mem_localDomain c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
      (originalGraph_analytic B b F x t c g d E j v)
end
end Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin
