import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyAwareOpenRestriction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HironakaG3EmptyAwareHistory HironakaSharpActualCurveComparisonRestriction

theorem emptyAware_openPreimage_eq {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (U : Opens X₂) :
    (openPreimage T₁ (preimageOpen Φ U) : Set Y₁) = ψ ⁻¹' (openPreimage T₂ U : Set Y₂) :=
  G3UniverseEmptyAwareOpenRestriction.emptyAware_openPreimage_eq h U

theorem emptyAware_open_restriction {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (U : Opens X₂) :
    EmptyAwareTowerIso (openRestriction Φ (preimageOpen Φ U) U rfl)
      (restrict (preimageOpen Φ U) T₁) (restrict U T₂)
      (openRestriction ψ (openPreimage T₁ (preimageOpen Φ U)) (openPreimage T₂ U)
        (emptyAware_openPreimage_eq h U)) :=
  G3UniverseEmptyAwareOpenRestriction.emptyAware_open_restriction h U


end
end Hironaka.HironakaG3EmptyAwareOpenRestriction
