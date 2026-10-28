/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.CanonicalCentres

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.CanonicalCentres

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.ResolutionInvariantSeq Hironaka.StepOnePhase
  Hironaka.StepOneWellFounded Hironaka.MaxOrderValue
  Hironaka.GeneralValue
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.MonomialInvariant (Val)

noncomputable section

variable {n : ℕ}

section Step

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- The invariant of the general step is the general value of the masked Step 1 value. -/
theorem generalStep_inv [WellFoundedLT Λ] (R : ResolutionInvariant.{u, v} n k Λ) (hn : 0 < n) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (generalStep R hn).inv 𝔪 T y =
      genInv (fun {X} 𝔍 {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R 𝔍 (Y := Y) T y) 𝔪 T y :=
  rfl

end Step

/-- The invariant in dimension `≤ k + 1` is the general step of the one in dimension `≤ k`. -/
theorem invFamily_succ (hn : 0 < n) (k : ℕ) : invFamily.{u} hn (k + 1) = generalStep (invFamily.{u} hn k) hn :=
  rfl

end

end Hironaka.CanonicalCentres
