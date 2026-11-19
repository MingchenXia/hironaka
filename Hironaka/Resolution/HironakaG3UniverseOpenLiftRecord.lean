import Hironaka.Resolution.HironakaG3UniverseChartTowerTransport
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseOpenLiftRecord
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseOpenDiffeo G3UniverseChartTowerTransport HironakaSmoothSubmersionContactParameterCoefficientIdeals
noncomputable section

/-- The actual open pullback factors through the literal lifted open record. -/
theorem openPullback_factors_lift {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U : Opens X₀)
    (M : MarkedIdeal n (CMfd.of (n := n) U)) (hI : M.ideal.IsCoherent) :
    markedPullback (m := n) (preimageDiffeo e U).symm M =
      markedPullback (m := n) (baseLiftDiffeo e U)
        (markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm M) := by
  have hh := whole_parameter_markedPullback_comp
    (X := CMfd.of (n := n) U) (Y := liftCMfd.{u} (CMfd.of (n := n) U))
    (Z := CMfd.of (n := n) (preimageOpens e U))
    (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm.contMDiff (baseLiftDiffeo e U).contMDiff M hI
  rw [← hh]
  have heq : (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm ∘ (baseLiftDiffeo e U) =
      (preimageDiffeo e U).symm := by
    funext x
    simp [baseLiftDiffeo]
  rw [heq]
end
end Hironaka.G3UniverseOpenLiftRecord
