import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyAwareCancellation
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3EmptyAwareHistory

/-- Cancel an actual final empty blowup on the right while retaining its endpoint map. -/
theorem strip_right_empty {n : ℕ} {X₁ X₂ Y₁ Y₂ Z₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂} {ρ : Z₂ → Y₂}
    (hρ : IsBlowupAlong n (∅ : Set Y₂) ρ)
    (φ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂) (hφ : ∀ z, φ z = ρ z)
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (h : EmptyAwareTowerIso Φ T₁ (.step T₂ ∅ ρ hρ) ψ) :
    EmptyAwareTowerIso Φ T₁ T₂ (ψ.trans φ) :=
  G3UniverseEmptyAwareCore.strip_right_empty hρ φ hφ h

end
end Hironaka.HironakaG3EmptyAwareCancellation
