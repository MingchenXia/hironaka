/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalIntrinsicUniqueness
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalChoiceNaturality

/-!
# Identity and composition for the entire original global smooth arrows

The global arrows are the actual noncompact original terminal constructions.
Literal equality of whole marked pullbacks supplies their source-identification
biholomorphism; intrinsic global uniqueness proves the functor laws. These laws
do not construct a globally scheduled noncompact history of blowups.
-/

set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSmoothSubmersionOriginalGlobalFunctor
noncomputable section

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOriginalGlobalMap
  HironakaSmoothSubmersionOriginalGlobalIntrinsicUniqueness
  HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalTerminalChoiceNaturality
  HironakaSmoothSubmersionOrderedChoiceImageTrace

open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n m ℓ : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}

/-- Equality of the entire original marked records transports their actual
terminal manifolds, with no new terminal choices or geometric certificates. -/
def terminalRecordEquiv (M N : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : IsInvDomain n N) (he : M = N) :
    originalTerminalManifold M hM ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      originalTerminalManifold N hN := by
  subst N
  exact Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (originalTerminalManifold M hM) ∞

theorem terminalRecordEquiv_proj (M N : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : IsInvDomain n N) (he : M = N)
    (z : originalTerminalManifold M hM) :
    originalTerminalGluedProjection N hN (terminalRecordEquiv M N hM hN he z) =
      originalTerminalGluedProjection M hM z := by
  subst N
  rfl

/-- Whole-record transport retains its actual identity and composition. -/
theorem terminalRecordEquiv_trans (M N P : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : IsInvDomain n N) (hP : IsInvDomain n P)
    (hMN : M = N) (hNP : N = P) :
    (terminalRecordEquiv M N hM hN hMN).trans (terminalRecordEquiv N P hN hP hNP) =
      terminalRecordEquiv M P hM hP (hMN.trans hNP) := by
  subst N
  subst P
  rfl

/-- The entire original global arrow over the identity is the actual
whole-record identity identification, without compactness or supplied history. -/
theorem originalGlobalSmoothMap_identity (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : X → X) :=
      Manifold.IsSubmersion.id
    let hN := original_ambient_domain_pullback hf M hM
    let he := whole_markedPullback_id M hM.isWellFormed.isCoherent
    originalGlobalSmoothMap hf M hM =
      terminalRecordEquiv (markedPullback (m := n) (id : X → X) M) M hN hM he := by
  dsimp only
  let hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : X → X) :=
    Manifold.IsSubmersion.id
  let N := markedPullback (m := n) (id : X → X) M
  let hN := original_ambient_domain_pullback hf M hM
  let he := whole_markedPullback_id M hM.isWellFormed.isCoherent
  let e := terminalRecordEquiv N M hN hM he
  exact originalGlobalSmoothCartesianMap_eq hf M hM _ e
    (originalGlobalSmoothMap_contMDiff hf M hM) e.contMDiff
    (originalGlobalSmoothMap_proj hf M hM)
    (terminalRecordEquiv_proj N M hN hM he)
    (originalGlobalSmoothMap_cartesian hf M hM)
    (holomorphicSquarePullback_biholomorphic_identity
      (originalTerminalGluedProjection M hM) (originalTerminalGluedProjection N hN) e
      (terminalRecordEquiv_proj N M hN hM he))

/-- The independently constructed entire global arrow of a composite equals
the actual composite after the genuine whole-marked-record identification.
Source, intermediate and target can all be noncompact. -/
theorem originalGlobalSmoothMap_composition {f : Y → X} {h : Z → Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hN := original_ambient_domain_pullback hf M hM
    let hP := original_ambient_domain_pullback hh (markedPullback (m := m) f M) hN
    let hfcomp := isSubmersion_composition hf hh
    let hQ := original_ambient_domain_pullback hfcomp M hM
    let he := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isWellFormed.isCoherent
    let e := terminalRecordEquiv (markedPullback (m := ℓ) (f ∘ h) M)
      (markedPullback (m := ℓ) h (markedPullback (m := m) f M)) hQ hP he
    originalGlobalSmoothMap hf M hM ∘
      originalGlobalSmoothMap hh (markedPullback (m := m) f M) hN ∘ e =
        originalGlobalSmoothMap hfcomp M hM := by
  dsimp only
  let N := markedPullback (m := m) f M
  let hN := original_ambient_domain_pullback hf M hM
  let P := markedPullback (m := ℓ) h N
  let hP := original_ambient_domain_pullback hh N hN
  let hfcomp := isSubmersion_composition hf hh
  let Q := markedPullback (m := ℓ) (f ∘ h) M
  let hQ := original_ambient_domain_pullback hfcomp M hM
  let he : Q = P := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isWellFormed.isCoherent
  let e := terminalRecordEquiv Q P hQ hP he
  let g := originalGlobalSmoothMap hf M hM
  let k := originalGlobalSmoothMap hh N hN
  have hpe := terminalRecordEquiv_proj Q P hQ hP he
  have hg := originalGlobalSmoothMap_proj hf M hM
  have hk := originalGlobalSmoothMap_proj hh N hN
  have hU := holomorphicSquarePullback_pasting
    (X := X) (D := originalTerminalManifold M hM)
    (Y := Y) (E := originalTerminalManifold N hN)
    (Z := Z) (F := originalTerminalManifold P hP)
    (f := f) (h := h) (a := g) (b := k)
    (originalTerminalGluedProjection N hN) (originalTerminalGluedProjection P hP)
    (originalTerminalGluedProjection M hM) hh.contMDiff
    (originalGlobalSmoothMap_contMDiff hh N hN) hk
    (originalGlobalSmoothMap_cartesian hf M hM) (originalGlobalSmoothMap_cartesian hh N hN)
  have hUe := holomorphicSquarePullback_biholomorphic_transport
    (X := X) (D := originalTerminalManifold M hM) (D' := originalTerminalManifold M hM)
    (Y := Z) (E := originalTerminalManifold P hP) (E' := originalTerminalManifold Q hQ)
    (f := f ∘ h) (g := g ∘ k)
    (originalTerminalGluedProjection P hP) (originalTerminalGluedProjection Q hQ)
    (originalTerminalGluedProjection M hM) (originalTerminalGluedProjection M hM)
    e (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (originalTerminalManifold M hM) ∞)
    hpe (fun _ => rfl) hU
  change HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback (f ∘ h)
    (g ∘ k ∘ e) (originalTerminalGluedProjection Q hQ)
      (originalTerminalGluedProjection M hM) at hUe
  apply originalGlobalSmoothCartesianMap_eq hfcomp M hM (g ∘ k ∘ e) _
    ((originalGlobalSmoothMap_contMDiff hf M hM).comp
      ((originalGlobalSmoothMap_contMDiff hh N hN).comp e.contMDiff))
    (originalGlobalSmoothMap_contMDiff hfcomp M hM) ?_
    (originalGlobalSmoothMap_proj hfcomp M hM) hUe
    (originalGlobalSmoothMap_cartesian hfcomp M hM)
  intro z
  change originalTerminalGluedProjection M hM (g (k (e z))) =
    f (h (originalTerminalGluedProjection Q hQ z))
  rw [hg, hk, hpe]

end
end Hironaka.HironakaSmoothSubmersionOriginalGlobalFunctor
