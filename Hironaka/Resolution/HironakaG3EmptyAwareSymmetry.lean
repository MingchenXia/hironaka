import Hironaka.Resolution.HironakaG3InteriorEmptyComparison
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyAwareSymmetry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3EmptyAwareHistory

/-- Reversing an empty-aware comparison exchanges left and right empty stages. -/
theorem symm {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) : EmptyAwareTowerIso Φ.symm T₂ T₁ ψ.symm :=
  G3UniverseEmptyAwareCore.symm h

end
end Hironaka.HironakaG3EmptyAwareSymmetry
