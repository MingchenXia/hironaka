import Hironaka.Resolution.HironakaClosedFootprintOpenTowerExtension
import Hironaka.Resolution.HironakaG3CentresOverGenericFactor
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3ClosedFootprintTransportedTower
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail MarkedIdealTowerTransport RestrictEmptyTower HironakaG3CentresOverGenericFactor
  HironakaClosedFootprintOpenTowerExtension

theorem extend_transported_closed_footprint_tower {n : ℕ} {X V Y : CMfd.{u} n}
    (U : Opens X) (F : Set X) (hF : IsClosed F) (hFU : F ⊆ U)
    (β : (CMfd.of (n := n) U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (T : BlowupTower V Y)
    (hT : CentresOver (β.symm ⁻¹' ((Subtype.val : U → X) ⁻¹' F)) T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z), CentresOver F Q ∧
      ∃ e : (transport β T).target ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso β (restrict U Q) T (e.symm.trans (transport β T).back) := by
  have hTrans := centresOver_of_isTowerIso (transport_isTowerIso β T)
    (β.symm ⁻¹' ((Subtype.val : U → X) ⁻¹' F)) hT
  have hEq : β ⁻¹' (β.symm ⁻¹' ((Subtype.val : U → X) ⁻¹' F)) =
      ((Subtype.val : U → X) ⁻¹' F) := by
    ext x
    simp only [mem_preimage, β.symm_apply_apply]
  rw [hEq] at hTrans
  obtain ⟨Z,Q,hQ,e,he,_,_⟩ := exists_closed_footprint_extension U F hF hFU (transport β T).tower hTrans
  refine ⟨Z,Q,hQ,e,?_⟩
  have hh := he.symm.trans (transport_isTowerIso β T)
  have hBase : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞).symm.trans β = β := by
    ext x
    rfl
  rw [hBase] at hh
  exact hh
end
end Hironaka.HironakaG3ClosedFootprintTransportedTower
