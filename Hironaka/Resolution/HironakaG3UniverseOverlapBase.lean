import Hironaka.Resolution.HironakaG3UniverseChartRestriction
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseOverlapBase
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsoTail MaxLocusLocal
  HironakaG3UniverseLiftManifold G3UniverseOpenDiffeo G3UniverseChartTowerTransport
  HironakaOriginalTerminalOverlapComparison G3UniverseChartRestriction
noncomputable section

/-- The joined base map on the common open is the actual overlap identification. -/
theorem lifted_overlap_base_eq {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U V : Opens X₀) :
    let W := U ⊓ V
    let hL : preimageOpens e W ≤ preimageOpens e U := fun _ h => h.1
    let hR : preimageOpens e W ≤ preimageOpens e V := fun _ h => h.2
    ((nestedLiftBase e U W).trans
      (((liftDiffeomorph.{u} (CMfd.of (n := n) (nestedOpens U W))).symm.trans
        (overlapBaseEquiv (n := n) (inf_le_left : W ≤ U) (inf_le_right : W ≤ V))).trans
        (liftDiffeomorph.{u} (CMfd.of (n := n) (nestedOpens V W))))).trans
      (nestedLiftBase e V W).symm = overlapBaseEquiv hL hR := by
  dsimp only
  ext p
  change e.symm (e p.val.val) = p.val.val
  exact e.symm_apply_apply _
end
end Hironaka.G3UniverseOverlapBase
