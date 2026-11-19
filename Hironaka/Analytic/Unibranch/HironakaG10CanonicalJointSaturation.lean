import Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding
import Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateAnalytic
import Hironaka.Resolution.HironakaG10JointNativeIdealMap

/-! Canonical joint-ideal saturation on the original recentered charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap
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
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateAnalytic
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding

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
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

abbrev targetOpen := recenteredTargetOpen c.embedding.dim t.rank j v (canonicalTargetOpen E.source.charts j)
abbrev originalGraph : Set (targetOpen B b F x t c g d E j v) :=
  (arbitraryBaseTargetMap c.embedding.dim t.rank j v (canonicalTargetOpen E.source.charts j)) ⁻¹'
    (coordinateSubset E.source.charts j (sourceGraphSet B b F x t c))

abbrev sourceDomain := realOpenChartDomain c.embedding.dim t.rank j (fun i => v i)
  (targetOpen B b F x t c g d E j v)

abbrev actualMap : sourceDomain B b F x t c g d E j v → productChartOpen E.target.charts j :=
  monomialAmbientFunction B b F x t c g d E j ∘ arbitraryCanonicalRecenteredChart E.source.charts j v hvj

abbrev targetStrict : Set (productChartOpen E.target.charts j) := targetStrictSet B b F x t c g d E j

theorem originalGraph_analytic : IsComplexAnalyticSubset (n := c.embedding.dim+t.rank)
    (originalGraph B b F x t c g d E j v) :=
  recenteredCoordinateSubset_analytic E.source.charts j v (sourceGraphSet B b F x t c) c.analytic

theorem targetStrict_analytic : IsComplexAnalyticSubset (n := t.embedding.dim+t.rank)
    (targetStrict B b F x t c g d E j) :=
  strict_chart_analytic E.target.charts t.positive (targetGraphSet B b t) t.analytic j

include M

theorem actualMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
      𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) ∞ (actualMap B b F x t c g d E j v hvj) :=
  (M.restricted_holomorphic j).comp (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).contMDiff

theorem actual_landing :
    realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) ⊆
        (actualMap B b F x t c g d E j v hvj) ⁻¹' (targetStrict B b F x t c g d E j) :=
  canonical_real_strict_landing B b F x t c g d E M j v hvj

variable (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)
  (z : sourceDomain B b F x t c g d E j v)
  (hz : z ∈ localDomain c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
      (originalGraph_analytic B b F x t c g d E j v))

include h0 hz

/-- The actual canonical joint ideal has the same whole pivot saturation as the strict ideal. -/
theorem native_joint_saturation
    (a : AmbientStalk c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) z) :
    a ∈ geometricStrictIdeal c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) z ↔
    ∃ m : ℕ, (exceptionalGerm c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) z)^m*a ∈
      rawAnalyticIdeal c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
        (originalGraph B b F x t c g d E j v) z ⊔
      Ideal.map ((ChartedSpace.locallyRingedSpaceMap (actualMap B b F x t c g d E j v hvj)
        (actualMap_holomorphic B b F x t c g d E M j v hvj)).stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := t.embedding.dim+t.rank)
          (targetStrict B b F x t c g d E j)) (actualMap B b F x t c g d E j v hvj z)) := by
  rw [←targetIdeal_eq_native_map (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (actualMap B b F x t c g d E j v hvj)
    (targetStrict B b F x t c g d E j) (actualMap_holomorphic B b F x t c g d E M j v hvj)
    (targetStrict_analytic B b F x t c g d E j) z]
  exact strict_mem_iff_joint_pivot_power (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j
    (fun i => v i) (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
    (originalGraph_analytic B b F x t c g d E j v)
    (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous
    (actual_landing B b F x t c g d E M j v hvj) z hz a

end
end Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
