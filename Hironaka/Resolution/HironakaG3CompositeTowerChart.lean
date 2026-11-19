import Hironaka.Resolution.HironakaG3TowerRestrictedQIdentification
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3CompositeTowerChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdealTowerTransport HironakaG3RTowerClass HironakaG3RigidOverLocalGlue

theorem composite_tower_chart_literal {n : ℕ} {X Z Y B : CMfd.{u} n}
    {P : Z → X} {Q : Y → Z} (hQ : Continuous Q)
    {𝒞 : LocalTowerClass X} (c : TowerChart 𝒞 Z P)
    (M : BlowupTower (CMfd.of (n := n) c.V) B)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (window Q hQ c.V))
    (hΦ : ∀ z, restrictedBaseMap Q hQ c.V (Φ z) = M.proj z) :
    let S := transport c.φ M
    let V := window Q hQ c.V
    (V : Set Y) = (P ∘ Q) ⁻¹' (c.U : Set X) ∧
    ∀ z, (P ∘ Q) ((S.back.trans Φ) z : Y) =
      (((c.T.append S.tower).proj z : c.U) : X) := by
  let S := transport c.φ M
  let V : Opens Y := window Q hQ c.V
  refine ⟨?_, ?_⟩
  · change Q ⁻¹' (c.V : Set Z) = (P ∘ Q) ⁻¹' (c.U : Set X)
    rw [c.V_eq]
    rfl
  · intro z
    have hp := proj_transport c.φ M z
    have hq := hΦ (S.back z)
    simp only [BlowupTower.proj_append, Function.comp_apply]
    change P (Q (Φ (S.back z) : Y)) = ((c.T.proj (S.tower.proj z) : c.U) : X)
    have hh := congrArg Subtype.val hq
    change Q (Φ (S.back z) : Y) = ((M.proj (S.back z) : c.V) : Z) at hh
    have hp' := congrArg Subtype.val hp
    calc
      P (Q (Φ (S.back z) : Y)) = P ((M.proj (S.back z) : c.V) : Z) := congrArg P hh
      _ = P (c.φ (S.tower.proj z) : Z) := congrArg P hp'.symm
      _ = ((c.T.proj (S.tower.proj z) : c.U) : X) := c.proj_φ _


theorem composite_tower_chart {n : ℕ} {X Z Y B : CMfd.{u} n} {P : Z → X} {Q : Y → Z}
    (hQ : Continuous Q) {𝒞 : LocalTowerClass X} (c : TowerChart 𝒞 Z P)
    (M : BlowupTower (CMfd.of (n := n) c.V) B)
    (Φ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ c.V))
    (hΦ : ∀ z, restrictedBaseMap Q hQ c.V (Φ z) = M.proj z) :
    ∃ (B' : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) c.U) B')
      (V : Opens Y), (V : Set Y) = (P ∘ Q) ⁻¹' (c.U : Set X) ∧
      ∃ e : B' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V,
        ∀ z, (P ∘ Q) (e z : Y) = ((T.proj z : c.U) : X) := by
  let S := transport c.φ M
  let V := window Q hQ c.V
  obtain ⟨hV,he⟩ := composite_tower_chart_literal hQ c M Φ hΦ
  exact ⟨S.target,c.T.append S.tower,V,hV,S.back.trans Φ,he⟩

end
end Hironaka.HironakaG3CompositeTowerChart
