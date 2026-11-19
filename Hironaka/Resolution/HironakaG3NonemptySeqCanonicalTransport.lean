import Hironaka.Resolution.HironakaG3NonemptyPhysicalCanonicalTransport
import Hironaka.Invariant.StepOneSeq
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe v
namespace Hironaka.G3NonemptySeqCanonicalTransport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3EmptyAwareHistory
  HironakaStageCenters MarkedIdeals G3NonemptyPhysicalCanonicalTransport
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

theorem isCanonical_of_emptyAware_nonempty_seq {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,v} n k Λ) {M : MarkedIdeal n X₂}
    (hM : IsInvDomain k M)
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
    (h₁ : StageCentres (fun _ C => C.Nonempty) T₁)
    (h₂ : StageCentres (fun _ C => C.Nonempty) T₂)
    (hcan : IsCanonical M (R.inv M) T₂) :
    IsCanonical (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M)
      (R.inv (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M)) T₁ :=
  Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hM Φ (isTowerIso_of_emptyAware_nonempty h h₁ h₂) hcan
end
end Hironaka.G3NonemptySeqCanonicalTransport
