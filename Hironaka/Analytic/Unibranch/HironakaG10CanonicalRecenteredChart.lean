import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
import Hironaka.Resolution.HironakaG10RecenteredMonomialBiholomorph

/-! Biholomorphic identification with the existing canonical product chart. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaRealOpenGeometricStrictSaturation HironakaG10RecenteredMonomialDomain
  HironakaG10RecenteredMonomialBiholomorph
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]
variable (a : ProductNormalCharts n r P) (j : Fin r)
variable (v : ComplexModel (n+r))
variable (hvt : ∀ i : Fin (n+r), i.val < n → v i = 0) (hvj : v (j.natAdd n) = 0)

/-- The literal actual target open of the existing product-normal chart. -/
def canonicalTargetOpen : Opens (ComplexModel (n+r)) :=
  ⟨(productNormalChart (n := n) a.base j).Φ.target,
    (productNormalChart (n := n) a.base j).Φ.isOpen_target⟩

/-- Same source-open, same actual target, and same normal monomial map. -/
theorem canonical_coordinate_open :
    monomialSourceOpen n r j (canonicalTargetOpen a j) = productCoordinateOpen a j := rfl

/-- This is the original product chart, not a newly chosen blowup model. -/
def canonicalRecenteredChart :
    realOpenChartDomain n r j (fun i => v i) (canonicalTargetOpen a j) ≃ₘ⟮
      𝓘(ℂ,ComplexModel (n+r)), 𝓘(ℂ,ComplexModel (n+r))⟯ productChartOpen a j := by
  let e := recenteredSourceDiffeomorph n r j v hvt hvj (canonicalTargetOpen a j)
  rw [canonical_coordinate_open a j] at e
  exact e.trans (productChartDiffeomorph a j).symm

/-- The actual canonical chart coordinates are the original translated vector. -/
theorem canonical_recentered_coordinates
    (w : realOpenChartDomain n r j (fun i => v i) (canonicalTargetOpen a j)) :
    productChartCoordinates a j (canonicalRecenteredChart a j v hvt hvj w) = w.val+v := by
  change productChartCoordinates a j
    ((productChartDiffeomorph a j).symm (recenteredSourceDiffeomorph n r j v hvt hvj
      (canonicalTargetOpen a j) w)) = w.val+v
  exact congrArg Subtype.val ((productChartDiffeomorph a j).apply_symm_apply
    (recenteredSourceDiffeomorph n r j v hvt hvj (canonicalTargetOpen a j) w))

end
end Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
