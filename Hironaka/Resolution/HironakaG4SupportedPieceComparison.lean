import Hironaka.Resolution.HironakaSupportedTowerPhysicalExtension
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaG3CentresOverGenericFactor

/-! Whole physical comparison of supported pieces over a given base map. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SupportedPieceComparison

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail MarkedIdealTowerTransport RestrictEmptyTower G3UniverseEmptyAwareCore G3UniverseEmptyAwareOpenRestriction
  HironakaSharpActualCurveComparisonRestriction HironakaG3CentresOverGenericFactor
  HironakaSupportedTowerPhysicalExtension

/-- A physical comparison on corresponding opens containing the footprints
extends over the whole pair of base manifolds and uses the given base map. -/
theorem emptyAware_extends_of_centresOver_biholomorphism {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    (e : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (U : Opens X₂) (K : Set X₂) (hKU : K ⊆ U)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (h₁ : CentresOver (e ⁻¹' K) T₁) (h₂ : CentresOver K T₂)
    {ψ : (CMfd.of (n := n) (openPreimage T₁ (preimageOpen e U)))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U))}
    (hψ : EmptyAwareTowerIso (openRestriction e (preimageOpen e U) U rfl)
      (restrict (preimageOpen e U) T₁) (restrict U T₂) ψ) :
    ∃ Ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso e T₁ T₂ Ψ := by
  let V := preimageOpen e U
  let R := transport e T₂
  let τ := openRestriction e V U rfl
  have hIso := emptyAware_of_isTowerIso (transport_isTowerIso e T₂)
  have hR := centresOver_of_isTowerIso (transport_isTowerIso e T₂) K h₂
  have hLoc := emptyAware_open_restriction hIso U
  have hV : e ⁻¹' K ⊆ V := fun _ hx => hKU hx
  have hCmp := G3UniverseEmptyAwareCore.trans hψ (G3UniverseEmptyAwareCore.symm hLoc)
  have hBase : τ.trans τ.symm = Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) V) ∞ := by
    apply Diffeomorph.ext
    intro z
    exact τ.symm_apply_apply z
  change EmptyAwareTowerIso (τ.trans τ.symm) (restrict V T₁) (restrict V R.tower) _ at hCmp
  rw [hBase] at hCmp
  obtain ⟨ξ, hξ, _⟩ := emptyAware_extends_of_centresOver V hV T₁ R.tower h₁ hR hCmp
  exact ⟨ξ.trans R.back, by simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hξ hIso⟩

theorem emptyAware_extends_of_matching_open {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    (e : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (U₁ : Opens X₁) (U₂ : Opens X₂) (hU : (U₁ : Set X₁) = e ⁻¹' (U₂ : Set X₂))
    (K : Set X₂) (hKU : K ⊆ U₂) (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (h₁ : CentresOver (e ⁻¹' K) T₁) (h₂ : CentresOver K T₂)
    {ψ : (CMfd.of (n := n) (openPreimage T₁ U₁))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U₂))}
    (hψ : EmptyAwareTowerIso (openRestriction e U₁ U₂ hU) (restrict U₁ T₁) (restrict U₂ T₂) ψ) :
    ∃ Ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso e T₁ T₂ Ψ := by
  have h : U₁ = preimageOpen e U₂ := SetLike.coe_injective hU
  subst U₁
  exact emptyAware_extends_of_centresOver_biholomorphism e U₂ K hKU T₁ T₂ h₁ h₂ hψ

end
end Hironaka.HironakaG4SupportedPieceComparison
