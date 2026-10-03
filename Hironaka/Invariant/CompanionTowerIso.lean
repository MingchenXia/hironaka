/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.ContactMarkedCanonical
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideal of the general step along isomorphisms of towers (property (6))

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol` and the commutativity of the
resolution with étale morphisms; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

The general step computes the value at a point of order `o ≥ 1` from the companion ideal `𝓞(𝔪_{T₀}, o)` formed at the
start stage `T₀`, restricted to an open set `W` (the mask), along the restricted tail `T₁|_W`.  Property (6) of the general
invariant compares this with the same construction for `Φ^*𝔪` along a tower isomorphic over a biholomorphism `Φ`.  An
isomorphism of towers `T₀'T₁' ≅ T₀T₁` splits as `T₀' ≅ T₀` over `Φ` (last-stage map `χ₀`) and `T₁' ≅ T₁` over `χ₀`
(`BlowupTowerSplitIso.IsTowerIso.exists_split`); with opens `W'`, `W` matched by `χ₀`:

* **`companionOf_isTowerIso`**: `𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'} = ψ^*(𝓞(𝔪_{T₀}, o)|_W)` for every biholomorphism `ψ : W' ≅ W` agreeing
  with `χ₀` (the transform along isomorphic towers, `IsTowerIso.geoTransformAlong_eq`, and `CompanionRebase`);
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.CompanionTowerIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.StepOneTangentChange Hironaka.NonmonomialOrderLocal Hironaka.InvDomainCompanion
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isCanonical_of_isTowerIso)

noncomputable section

variable {n : ℕ}

section Iso

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔪 : MarkedIdeal n X}
  {Y₀' Y₀ : CMfd.{u} n} {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
  {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀}

/-- **The companion ideal along an isomorphism of towers** (property (6), marked ideals): for `T₀' ≅ T₀` over `Φ : X' ≅ X`
with last-stage map `χ₀`, `T₀` a multiple test blow-up of `𝔪` (in the domain, `n > 0`, `o ≥ 1`), opens `W'`, `W` of the
two last stages and `ψ : W' ≅ W` agreeing with `χ₀`: `𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'} = ψ^*(𝓞(𝔪_{T₀}, o)|_W)`. -/
theorem companionOf_isTowerIso (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o)
    (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower 𝔪 T₀) (W' : Opens Y₀') (W : Opens Y₀)
    (ψ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hψ : ∀ q : W', ((ψ q : W) : Y₀) = χ₀ q) :
    MarkedIdeal.pullback (Subtype.val : W' → Y₀') (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o) =
      MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)) := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hcoh : (companionOf n (geoTransformAlong 𝔪 T₀) o).ideal.IsCoherent :=
    (isInvDomain_companionAlong hn hdomT ho).isWellFormed.isCoherent
  rw [IsTowerIso.geoTransformAlong_eq Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hT₀,
    ← pullback_diffeo_companionOf hn χ₀ hdomT.isWellFormed hdomT.isNonzeroAlongAt o]
  exact ContactMarkedCanonical.pullback_pullback_of_comp_eq hcoh χ₀.contMDiff contMDiff_subtype_val ψ.contMDiff
    contMDiff_subtype_val fun q => (hψ q).symm

end Iso

end

end Hironaka.CompanionTowerIso
