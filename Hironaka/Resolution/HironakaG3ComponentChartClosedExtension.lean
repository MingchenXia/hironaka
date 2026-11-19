import Hironaka.Resolution.HironakaG3ClosedFootprintTransportedTower
import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Invariant.MaxLocusLocal
set_option autoImplicit false
namespace Hironaka.HironakaG3ComponentChartClosedExtension
noncomputable section
open Set Function TopologicalSpace Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdealTowerTransport RestrictEmptyTower HironakaG3RTowerClass
  MaxLocusLocal HironakaG3ClosedFootprintTransportedTower
open scoped Topology Manifold ContDiff
theorem component_chart_closed_extension {n : ℕ} {X Z : CMfd.{0} n}
    (C : Set X) (hC : IsClosed C) (A W : Opens X) (hCW : C ⊆ W)
    (𝒞 : LocalTowerClass X) {P : Z → X} (c : TowerChart 𝒞 Z P)
    (hc : c.U = W ⊓ A) (hCentres : CentresOver ((Subtype.val : c.U → X) ⁻¹' C) c.T) :
    let V : Opens A := nestedOpens A c.U
    let β := nestedOpensDiffeo (n := n) (show c.U ≤ A by rw [hc]; exact inf_le_right)
    ∃ (Y : CMfd.{0} n) (Q : BlowupTower (CMfd.of (n := n) A) Y),
      CentresOver ((Subtype.val : A → X) ⁻¹' C) Q ∧
      ∃ e : (transport β c.T).target ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q V,
        IsTowerIso β (restrict V Q) c.T (e.symm.trans (transport β c.T).back) := by
  dsimp only
  let V : Opens A := nestedOpens A c.U
  have hUA : c.U ≤ A := by rw [hc]; exact inf_le_right
  let β := nestedOpensDiffeo (n := n) hUA
  let F : Set A := (Subtype.val : A → X) ⁻¹' C
  have hF : IsClosed F := hC.preimage continuous_subtype_val
  have hFV : F ⊆ V := by
    intro x hx
    change x.val ∈ c.U
    rw [hc]
    exact ⟨hCW hx,x.property⟩
  have hEq : β.symm ⁻¹' ((Subtype.val : V → A) ⁻¹' F) = (Subtype.val : c.U → X) ⁻¹' C := by
    ext x
    rfl
  have hT : CentresOver (β.symm ⁻¹' ((Subtype.val : V → A) ⁻¹' F)) c.T := by
    rw [hEq]
    exact hCentres
  exact extend_transported_closed_footprint_tower
    (X := CMfd.of (n := n) A) (V := CMfd.of (n := n) c.U) (Y := c.Y)
    V F hF hFV β c.T hT
end
end Hironaka.HironakaG3ComponentChartClosedExtension
