import Hironaka.Resolution.HironakaG3TowerRestrictedQIdentification
import Hironaka.Resolution.HironakaG3RGluedBoundary
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3RestrictTowerChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdealTowerTransport BlowupTowerIsoTail HironakaG3RTowerClass HironakaG3RigidOverLocalGlue
  HironakaG3RGluedBoundary MaxLocusLocal

theorem restrict_tower_chart {n : ℕ} {X Z : CMfd.{u} n} {P : Z → X} (hP : Continuous P)
    {𝒞 : LocalTowerClass X} (c : TowerChart 𝒞 Z P) (U : Opens X) (hU : U ≤ c.U) :
    ∃ c' : TowerChart (fun _ _ _ => True) Z P,
      c'.U = U ∧ c'.V = window P hP U := by
  let W : Opens Z := window P hP U
  have hW : W ≤ c.V := by
    intro z hz
    change z ∈ (c.V : Set Z)
    rw [c.V_eq]
    exact hU hz
  let V : Opens c.U := nestedOpens c.U U
  let R : Opens c.V := nestedOpens c.V W
  have hEq : preimageOpens c.φ R = openPreimage c.T V := by
    apply Opens.ext
    ext z
    change P (c.φ z : Z) ∈ U ↔ (c.T.proj z : X) ∈ U
    rw [c.proj_φ]
  let e := (opensCongr (n := n) hEq.symm).trans (preimageDiffeo c.φ R).symm
  let η := nestedOpensDiffeo (n := n) hW
  let β := (nestedOpensDiffeo (n := n) hU).symm
  let S := transport β (restrict V c.T)
  let φ := S.back.trans (e.trans η)
  refine ⟨⟨U,S.target,S.tower,True.intro,W,rfl,φ,?_⟩,rfl,rfl⟩
  intro z
  have hp := proj_transport β (restrict V c.T) z
  have hr := proj_restrict V c.T (S.back z)
  change P ((η (e (S.back z)) : W) : Z) = ((S.tower.proj z : U) : X)
  have hc := c.proj_φ (S.back z).val
  have h2 := congrArg (fun q : V => ((q : c.U) : X)) hp
  have h3 := congrArg Subtype.val hr
  exact hc.trans (h3.symm.trans h2.symm)
end
end Hironaka.HironakaG3RestrictTowerChart
