import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareNonempty
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe v
namespace Hironaka.G3NonemptyPhysicalCanonicalTransport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaG3EmptyAwareHistory HironakaStageCenters MarkedIdeals MarkedIdeals.MarkedIdeal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- If both actual histories have no empty stage, an empty-aware comparison is a stagewise tower isomorphism. -/
theorem isTowerIso_of_emptyAware_nonempty {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
    (h₁ : StageCentres (fun _ C => C.Nonempty) T₁)
    (h₂ : StageCentres (fun _ C => C.Nonempty) T₂) :
    IsTowerIso Φ T₁ T₂ ψ :=
  G3UniverseEmptyAwareNonempty.isTowerIso_of_emptyAware_nonempty h h₁ h₂

/-- Canonicality transfers for an actual empty-aware comparison when both histories have only nonempty stages. -/
theorem isCanonical_of_emptyAware_nonempty {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (R : ResolutionInvariantExt.ResolutionInvariant.{0,v} n k Λ) {M : MarkedIdeal n X₂}
    (hM : IsInvDomain k M)
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
    (h₁ : StageCentres (fun _ C => C.Nonempty) T₁)
    (h₂ : StageCentres (fun _ C => C.Nonempty) T₂)
    (hcan : IsCanonical M (R.inv M) T₂) :
    IsCanonical (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M) (R.inv (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M)) T₁ :=
  ResolutionInvariantExt.isCanonical_of_isTowerIso R hM Φ (isTowerIso_of_emptyAware_nonempty h h₁ h₂) hcan
end
end Hironaka.G3NonemptyPhysicalCanonicalTransport
