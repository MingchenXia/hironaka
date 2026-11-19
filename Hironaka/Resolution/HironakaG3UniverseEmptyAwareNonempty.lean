import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaStageCenters
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseEmptyAwareNonempty
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaStageCenters G3UniverseEmptyAwareCore

/-- If both actual histories have no empty stage, their empty-aware comparison
is a stagewise tower isomorphism with the same endpoint map. -/
theorem isTowerIso_of_emptyAware_nonempty {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
    (h₁ : StageCentres (fun _ C => C.Nonempty) T₁)
    (h₂ : StageCentres (fun _ C => C.Nonempty) T₂) :
    IsTowerIso Φ T₁ T₂ ψ := by
  induction h with
  | refl => exact .refl
  | step h hπ₁ hπ₂ χ hcomm hC ih => exact .step (ih h₁.1 h₂.1) hπ₁ hπ₂ χ hcomm hC
  | leftEmpty h hπ φ hφ ih => exact False.elim (Set.not_nonempty_empty h₁.2)
  | rightEmpty h hπ φ hφ ih => exact False.elim (Set.not_nonempty_empty h₂.2)
end
end Hironaka.G3UniverseEmptyAwareNonempty
