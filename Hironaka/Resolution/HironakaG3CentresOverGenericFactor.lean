import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3CentresOverGenericFactor
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupRestrictOpen RestrictEmptyTower
  BlowupTowerIsomorphism

variable {n : ℕ} {X : CMfd.{u} n}

theorem centresOver_restrict (U : Opens X) (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T →
      CentresOver ((Subtype.val : U → X) ⁻¹' F) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => by
      refine ⟨centresOver_restrict U F T h.1, ?_⟩
      intro y hy
      change ((restrict U T).proj y).val ∈ F
      rw [proj_restrict]
      exact h.2 hy

theorem centresOver_of_isTowerIso {X' Y' Y : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (F : Set X) :
    CentresOver F T → CentresOver (Φ ⁻¹' F) T' := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro h
    refine ⟨ih h.1, ?_⟩
    intro y hy
    have hyC : χ y ∈ C := by change y ∈ χ ⁻¹' C; rw [hC]; exact hy
    change Φ (T'.proj y) ∈ F
    rw [hiso.proj_comm]
    exact h.2 hyC
end
end Hironaka.HironakaG3CentresOverGenericFactor
