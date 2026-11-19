import Hironaka.Resolution.HironakaG3EmptyAwareCancellation
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyAwareComposition
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareCancellation

/-- Empty-aware comparisons compose with their literal endpoint maps. -/
theorem trans {n : ℕ} {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CMfd.{0} n}
    {Φ₁ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {Φ₂ : X₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂} {T₃ : BlowupTower X₃ Y₃}
    {ψ₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    {ψ₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₃}
    (h₁ : EmptyAwareTowerIso Φ₁ T₁ T₂ ψ₁) (h₂ : EmptyAwareTowerIso Φ₂ T₂ T₃ ψ₂) :
    EmptyAwareTowerIso (Φ₁.trans Φ₂) T₁ T₃ (ψ₁.trans ψ₂) :=
  G3UniverseEmptyAwareCore.trans h₁ h₂

end
end Hironaka.HironakaG3EmptyAwareComposition
