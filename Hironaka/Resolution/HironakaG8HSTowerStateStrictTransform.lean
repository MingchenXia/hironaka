import Hironaka.Resolution.HironakaG11PresTowerState
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8HSTowerStateStrictTransform
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal HironakaG11PresTowerState HomogenizedGlueingTower
variable {n : ℕ} {X : CMfd.{0} n}

/-- A native HS tower state itself identifies its iterated strict transforms
with the geometric strict transform of the whole tower projection. -/
theorem hsTowerState_strictAlong_eq_strictTransform (Q : MarkedIdeal n X) {W : Set X}
    (hW : IsClosed W) {H : ℕ → ℕ} (hs : HSTowerState Q W H) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      strictAlong T W = strictTransform n T.proj W
  | _, .refl, _ => (strictTransform_id hW).symm
  | _, .step T C π hπ, hT => by
    obtain ⟨hTt, hC⟩ := hT
    have ih := hsTowerState_strictAlong_eq_strictTransform Q hW hs T hTt
    have hA := (hs T hTt).1
    have hSing := (hs T hTt).2.2.2.2
    rw [ih] at hA hSing
    have hthin : strictTransform n T.proj W ⊆ closure (strictTransform n T.proj W \ C) :=
      (HironakaResolutionSpace.subset_closure_diff_singularSet hA).trans
        (closure_mono (sdiff_subset_sdiff_right (hC.2.1.trans hSing)))
    rw [strictAlong_step, ih, BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hthin,
      BlowupTower.proj_step, StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff W]
end
end Hironaka.HironakaG8HSTowerStateStrictTransform
