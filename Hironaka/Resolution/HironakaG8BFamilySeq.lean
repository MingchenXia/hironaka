import Hironaka.Resolution.HironakaG11InvBMRestrictOpen
import Hironaka.Invariant.StepOneSeq

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value for a lower invariant with per-sequence local finiteness

Blueprint `hironaka-g8b-family-invariants.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c, "Modules 10--13
against lane G11C's target", module 12 (repair (B'), human decision on I-1304).

The modules of lane G11B for Bierstone--Milman's lower family (`HironakaG11InvBMMask` ... `HironakaG11InvBMTangentIndep`,
`HironakaG11InvBMNaturality`, `HironakaG11InvBMRestrictOpen`) state
the Step 1 value `HironakaG11InvBMLower.stepOneInvBM R` and its properties for a lower invariant
`R : ResolutionInvariantExt.ResolutionInvariant n (k - 1) Λ` (uniform property (8)).  The class-functorial invariants
(`HironakaG11InvBMClass.BMInvariant`) carry a `ResolutionInvariantSeq.ResolutionInvariant` (per-sequence property (8')), as does
the induction on the dimension (`CanonicalCentres.ofWellFounded`).  As for Włodarczyk's Step 1 value (`StepOneSeq`), the command
`transport_ext_to_seq_module` (`ExtSeqTransport`) adds, for every declaration of these modules that depends on
`ResolutionInvariantExt.ResolutionInvariant`, a kernel-checked copy in the namespace `Hironaka.Seq`
(`Seq.HironakaG11InvBMLower.stepOneInvBM`, `Seq.HironakaG11InvBMTangentIndep.TangentIndepBM`,
`Seq.HironakaG11InvBMBridge.admissible_field`, ...), stated for `R : ResolutionInvariantSeq.ResolutionInvariant`.  That the
command succeeds shows that **none of these proofs uses property (8) of the lower invariant**.

**Coordination.**  A later module that transports further modules of the family (the maximal-order value, the independence of
the tangent direction, the class functoriality of the Step 1 value) must import this module: the command then reuses the
constants transported here (a second, independent transport of the same constants would clash on import).

## Main results (stated here as ordinary theorems)

* `stepOneInvBM_ofExt`, `tangentIndepBM_ofExt`: for an invariant of the old structure, the transported value and the transported
  independence of the tangent direction of `ofExt R` are those of `R` (by `rfl`);
* `exists_isGeoResolution_stepOneInvBM`: resolution of the marked ideals of maximal order by a canonical segment of
  Bierstone--Milman's Step 1 value, for a lower invariant of the new structure (given the anchor change).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Hironaka.ExtSeqTransport

/-! ### The transport of Bierstone--Milman's Step 1 stack -/

transport_ext_to_seq_module
  Hironaka.Resolution.HironakaG11InvBMMask Hironaka.Resolution.HironakaG11InvBMMaskStep
  Hironaka.Resolution.HironakaG11InvBMLower Hironaka.Resolution.HironakaG11InvBMRebase
  Hironaka.Resolution.HironakaG11InvBMCanonicalTail Hironaka.Resolution.HironakaG11InvBMUSC
  Hironaka.Resolution.HironakaG11InvBMAdmissible Hironaka.Resolution.HironakaG11InvBMBridge
  Hironaka.Resolution.HironakaG11InvBMTangentIndep Hironaka.Resolution.HironakaG11InvBMNaturality
  Hironaka.Resolution.HironakaG11InvBMRestrictOpen

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG8BFamilySeq

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.ResolutionInvariantSeq
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (IsCanonicalSegment)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The transported Step 1 value extends the old one**: for an invariant `R` of the old structure, Bierstone--Milman's Step 1
value of `ofExt R` is that of `R`. -/
theorem stepOneInvBM_ofExt (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    Seq.HironakaG11InvBMLower.stepOneInvBM (ResolutionInvariant.ofExt R) 𝔍 T y =
      HironakaG11InvBMLower.stepOneInvBM R 𝔍 T y :=
  rfl

/-- **The transported independence of the tangent direction extends the old one.** -/
theorem tangentIndepBM_ofExt (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n (k - 1) Λ)
    (𝔍 : MarkedIdeal n X) :
    Seq.HironakaG11InvBMTangentIndep.TangentIndepBM (k := k) 𝔍 (ResolutionInvariant.ofExt R) ↔
      HironakaG11InvBMTangentIndep.TangentIndepBM (k := k) 𝔍 R :=
  Iff.rfl

/-- **Resolution of the marked ideals of maximal order by Bierstone--Milman's Step 1 value**, for a lower invariant of the new
structure: with well-founded values and the anchor change, a canonical segment of `stepOneInvBM R 𝔍` resolves `𝔍` over a
compact base. -/
theorem exists_isGeoResolution_stepOneInvBM [CompactSpace X] [WellFoundedLT Λ]
    (R : ResolutionInvariant.{u, v} n (k - 1) Λ) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (hAC : Seq.HironakaG11InvBMCanonicalTail.AnchorChangeBM 𝔍 R) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment 𝔍 (Seq.HironakaG11InvBMLower.stepOneInvBM R 𝔍) T ∧ IsGeoResolution 𝔍 T :=
  Seq.HironakaG11InvBMBridge.exists_isGeoResolution_stepOneInvBM R 𝔍 hAC h hmax hn

end

end Hironaka.HironakaG8BFamilySeq
