/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ExtSeqTransport
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.StepOnePhase
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.ContactEmptyPrefix
import Hironaka.Invariant.ContactLowerValue
import Hironaka.Invariant.ContactMarkedCanonical
import Hironaka.Invariant.ContactRepresentative
import Hironaka.Invariant.ContactStageKept
import Hironaka.Invariant.ContactStageRebase
import Hironaka.Invariant.InvDomainRebase
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MaximalOrderStepOneB
import Hironaka.Invariant.MemberRestrictTowerIso
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.StepOneAdmissible
import Hironaka.Invariant.StepOneAdmissibleTop
import Hironaka.Invariant.StepOneBridge
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Invariant.StepOneCompare
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneRepresentative
import Hironaka.Invariant.StepOneRestrictOpen
import Hironaka.Invariant.StepOneSpecialDrop
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Invariant.StepOneTowerIso
import Hironaka.Invariant.StepOneUSC
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
import Hironaka.Invariant.StepOneWellFounded
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Step 1 (maximal-order) value for a lower invariant with per-sequence local finiteness

The Step 1 value `stepOneInvM` and its properties were formalized for a lower invariant `R:
ResolutionInvariantExt.ResolutionInvariant n (k - 1) Λ` (uniform (8)), which the induction of
`hir:canonical-centres` cannot supply.

**The Step 1 stack for the new structure.**  The command `transport_ext_to_seq_module` (`ExtSeqTransport`) adds, for every
declaration of the modules listed below that depends on `ResolutionInvariantExt.ResolutionInvariant`, a kernel-checked copy in
the namespace `Hironaka.Seq` (e.g. `Seq.StepOneValueMasked.stepOneInvM`,
`Seq.StepOneBridge.admissible_field`, `Seq.MaxOrderValue.isMaxOrderValue_stepOneInvM`), stated for
`R : ResolutionInvariantSeq.ResolutionInvariant`, with `R.f` replaced by `R.isInvValue.f` for the fields (1)--(7), (4').  That the
command succeeds shows that none of these proofs uses property (8) of the lower invariant.

## Main results (stated here as ordinary theorems)

* **`isMaxOrderValue_stepOneInvM`**: for `R : ResolutionInvariantSeq.ResolutionInvariant n (k - 1) Λ` and `0 < n`, the masked
  Step 1 value `Seq.StepOneValueMasked.stepOneInvM R` is a value function for the marked ideals of maximal order in dimension
  `≤ k` (`MaxOrderValue.IsMaxOrderValue`);
* `isAdmissibleCentre_maxLocus_stepOneInvM`: the drop along canonical segments, the admissibility of the maximum
  locus, and the resolution of a marked ideal of maximal order for well-founded `Λ` (`StepOneWellFounded`), for the
  new structure.
-/

open Hironaka.ExtSeqTransport

/-! ### The transport of the Step 1 stack -/

transport_ext_to_seq_module
  Hironaka.Blowup.BlowupTowerSplit
  Hironaka.Invariant.MaxLocusLocal
  Hironaka.Invariant.InvDomainRebase
  Hironaka.Invariant.MaximalOrderStepOneB
  Hironaka.Invariant.ContactStageRebase
  Hironaka.Invariant.ContactMarkedCanonical
  Hironaka.Invariant.ContactRepresentative
  Hironaka.Invariant.ContactStageKept
  Hironaka.Invariant.ContactEmptyPrefix
  Hironaka.Invariant.ContactLowerValue
  Hironaka.Invariant.MemberRestrictTowerIso
  Hironaka.Invariant.CompanionRebase
  Hironaka.Invariant.NonmonomialOrderRegime
  Hironaka.Invariant.StepOneValue
  Hironaka.Invariant.StepOneNearby
  Hironaka.Invariant.StepOneValueMasked
  Hironaka.Invariant.StepOneCompare
  Hironaka.Invariant.StepOneTangentChange
  Hironaka.Invariant.StepOneCanonicalTail
  Hironaka.Invariant.StepOneUSC
  Hironaka.Invariant.StepOneAdmissibleTop
  Hironaka.Invariant.StepOneSpecialDrop
  Hironaka.Invariant.StepOneAdmissible
  Hironaka.Invariant.StepOneEmptyPrefix
  Hironaka.Invariant.StepOneRepresentative
  Hironaka.Invariant.StepOneRestrictOpen
  Hironaka.Invariant.StepOneTowerIso
  Hironaka.Invariant.StepOneBridge
  Hironaka.Invariant.StepOneWellFounded
  Hironaka.Invariant.StepOnePhase
  Hironaka.Invariant.MaxOrderValue

transport_ext_to_seq
  Hironaka.ResolutionInvariantExt.isAdmissibleCentre_maxLocus
  Hironaka.ResolutionInvariantExt.isGeoTestTower_of_isCanonical
  Hironaka.ResolutionInvariantExt.isInvDomain_of_isCanonical
  Hironaka.ResolutionInvariantExt.isCanonical_restrict
  Hironaka.ResolutionInvariantExt.isCanonical_of_isTowerIso
  Hironaka.ResolutionInvariantExt.isCanonical_append_iff

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneSeq

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MaxOrderValue Hironaka.ResolutionInvariantSeq Hironaka.StepOneWellFounded
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The masked Step 1 value of a lower invariant of the new structure is a value function for the marked ideals of
maximal order** (`hir:step-one-seq`; `0 < n`): properties (1)--(7), (4') along its canonical segments, for every marked ideal
of the domain in dimension `≤ k` of maximal order along its submanifold. -/
theorem isMaxOrderValue_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (hn : 0 < n) :
    IsMaxOrderValue n k (fun {X} 𝔍 {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R 𝔍 (Y := Y) T y) :=
  Seq.MaxOrderValue.isMaxOrderValue_stepOneInvM R hn

end

end Hironaka.StepOneSeq
