/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.StepOneSeq
import Hironaka.Support.StepOneDropExtExact

open Hironaka.ExtSeqTransport
transport_ext_to_seq Hironaka.StepOneWellFounded.stepDrop_stepOneInvM

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneSeq

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MaxOrderValue Hironaka.ResolutionInvariantSeq
  Hironaka.StepOneWellFounded
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The value drops along canonical segments** (the hypothesis of the well-founded driver), for the new structure. -/
theorem stepDrop_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    StepDrop 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) :=
  Seq.StepOneWellFounded.stepDrop_stepOneInvM R 𝔍 h hmax hn

end
end Hironaka.StepOneSeq
