import Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
import Hironaka.Resolution.HironakaG10ArbitraryBaseRecenter

/-! The original canonical product chart at arbitrary exceptional base coordinates. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
noncomputable section
open Hironaka Hironaka
  HironakaRealOpenGeometricStrictSaturation HironakaG10ArbitraryBaseRecenter
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]
variable (a : ProductNormalCharts n r P) (j : Fin r)
variable (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)

/-- The actual canonical source chart at any exceptional base, after translating its target. -/
def arbitraryCanonicalRecenteredChart :
    realOpenChartDomain n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) ≃ₘ⟮
      𝓘(ℂ,ComplexModel (n+r)), 𝓘(ℂ,ComplexModel (n+r))⟯ productChartOpen a j := by
  let e := arbitraryBaseSourceDiffeomorph n r j v hvj (canonicalTargetOpen a j)
  rw [canonical_coordinate_open a j] at e
  exact e.trans (productChartDiffeomorph a j).symm

/-- Every actual canonical coordinate is the original translated vector. -/
theorem arbitrary_canonical_recentered_coordinates
    (w : realOpenChartDomain n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j))) :
    productChartCoordinates a j (arbitraryCanonicalRecenteredChart a j v hvj w) = w.val+v := by
  change productChartCoordinates a j
    ((productChartDiffeomorph a j).symm (arbitraryBaseSourceDiffeomorph n r j v hvj
      (canonicalTargetOpen a j) w)) = w.val+v
  exact congrArg Subtype.val ((productChartDiffeomorph a j).apply_symm_apply
    (arbitraryBaseSourceDiffeomorph n r j v hvj (canonicalTargetOpen a j) w))

end
end Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
