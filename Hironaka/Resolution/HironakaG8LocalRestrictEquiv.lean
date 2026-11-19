import Hironaka.Resolution.HironakaG8LocalPower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restricted-equivalent marked ideals are locally equivalent (G8 lane, run 0080, round 4; (B') ports, glue)

Blueprint: `hironaka-g8-resume-local-restrict-equivalence.tex`.

Several objects of the (B') repair are known only up to `MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv` (same carrier,
boundary and mark, ideals agreeing on the carrier): e.g. `HironakaG11InvBMStage.restrictEquiv_stage_contactCoeffBM` compares
the family's `contactCoeffBM` with Bierstone--Milman's transform of `𝒞_U(I_∅)`.  This module records that such marked
ideals are locally equivalent for every kind of local test history without exceptional blowups
(`locEquiv_of_restrictEquiv`, `locWPEquiv_of_restrictEquiv`), from the power relation of `HironakaG8LocalPower` with
exponent `1`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalRestrictEquiv

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.IdealWeightPowers (idealPow)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open Hironaka.HironakaG8LocalPower (isLocStable_powerRel)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} {κ : Kinds}

/-- **Restricted-equivalent marked ideals of the native domain are locally equivalent** (kinds without exceptional
blowups). -/
theorem locEquiv_of_restrictEquiv (hexc : κ.exc = false) {k k' : ℕ} {P Q : MarkedIdeal n X} (hP : IsInvDomain k P)
    (hQ : IsInvDomain k' Q) (h : RestrictEquiv P Q) : LocEquiv κ P Q := by
  have hpow1 : idealPow P.ideal 1 = P.ideal :=
    FactorizationFromResolution.idealPow_one_of_isCoherent hP.isWellFormed.isCoherent
  refine LocEquiv.of_isLocStable (isLocStable_powerRel κ) hexc ⟨k, k', 1, le_rfl, hP, hQ, ?_⟩
  obtain ⟨hN, hE, hd, hle, hge⟩ := h
  refine ⟨hN.symm, hE.symm, ?_, ?_, ?_⟩
  · show Q.d = P.d * 1
    rw [Nat.mul_one]
    exact hd.symm
  · show RestrictLe Q.N Q.ideal (idealPow P.ideal 1)
    rw [hpow1, ← hN]
    exact hge
  · show RestrictLe Q.N (idealPow P.ideal 1) Q.ideal
    rw [hpow1, ← hN]
    exact hle

/-- **The `LocWPEquiv` form.** -/
theorem locWPEquiv_of_restrictEquiv {k k' : ℕ} {P Q : MarkedIdeal n X} (hP : IsInvDomain k P) (hQ : IsInvDomain k' Q)
    (h : RestrictEquiv P Q) : LocWPEquiv P Q :=
  locEquiv_of_restrictEquiv rfl hP hQ h

end

end Hironaka.HironakaG8LocalRestrictEquiv
