import Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction

/-! Actual canonical strict landing in the same recentered real-open chart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf HironakaReducedComplexAnalyticSpaces
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotObjects
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy

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
  (M : AllAmbientMonomialLiftData B b F x t c g d E)

include M

/-- Landing is derived from the actual same canonical blowup square and its original charts. -/
theorem canonical_real_strict_landing (j : Fin t.rank)
    (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0) :
    realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
      (recenteredTargetOpen c.embedding.dim t.rank j v (canonicalTargetOpen E.source.charts j))
      ((arbitraryBaseTargetMap c.embedding.dim t.rank j v (canonicalTargetOpen E.source.charts j)) ⁻¹'
        (coordinateSubset E.source.charts j (sourceGraphSet B b F x t c))) ⊆
      (monomialAmbientFunction B b F x t c g d E j ∘
        arbitraryCanonicalRecenteredChart E.source.charts j v hvj) ⁻¹'
        (targetStrictSet B b F x t c g d E j) := by
  intro z hz
  rw [original_strict_carrier_conjugacy E.source.charts j v hvj (sourceGraphSet B b F x t c)] at hz
  exact monomial_strict_landing B b F x t c g d E M j _ hz

omit M in
/-- The actual source-chart point puts zero in its genuinely translated target. -/
theorem canonical_target_origin (j : Fin t.rank) (z : productChartOpen E.source.charts j) :
    (0 : ComplexModel (c.embedding.dim+t.rank)) ∈
      recenteredTargetOpen c.embedding.dim t.rank j
        (productChartCoordinates E.source.charts j z) (canonicalTargetOpen E.source.charts j) := by
  have hz := ((productChartDiffeomorph E.source.charts j) z).property
  change BlowupMonomialCharts.monomial c.embedding.dim (j.natAdd c.embedding.dim)
    (productChartCoordinates E.source.charts j z) ∈ canonicalTargetOpen E.source.charts j at hz
  change (0 : ComplexModel (c.embedding.dim+t.rank)) +
    BlowupMonomialCharts.monomial c.embedding.dim (j.natAdd c.embedding.dim)
      (productChartCoordinates E.source.charts j z) ∈ canonicalTargetOpen E.source.charts j
  simpa using hz

end
end Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding
