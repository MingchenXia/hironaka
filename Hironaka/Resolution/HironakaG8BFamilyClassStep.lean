import Hironaka.Resolution.HironakaG8BFamily
import Hironaka.Resolution.HironakaG8ClassStep

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The class-functorial induction with plan module 10 reduced to the class data of the lower ideals

Blueprint `hironaka-g8b-family-invariants.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c (module 12);
lane G8C's skeleton of plan module 10 (`HironakaG8ClassStep`, inbox I-1361 C-0001).

Lane G8C proved plan module 10 (`classFunctorialMaxOrder_stepOneInvBM`) from the class data of the lower ideals of two
class-equivalent marked ideals (`HironakaG8ClassStep.LowerClassBM A B`, a statement that does not mention the lower invariant:
on every common open of the masks the two restricted lower ideals are `LocWPEquiv`, with carriers of the same dimension and
agreeing boundary exponents; Bierstone--Milman 2008, §5 Steps I.A, I.B).  Its module transports to the structure
`ResolutionInvariantSeq.ResolutionInvariant` (`transport_ext_to_seq_module`, reusing the constants of `HironakaG8BFamilySeq`):
**none of its proofs uses property (8)**.  So the input `ClassStepBM` of the induction (`HironakaG8BFamily`) follows from the
`R`-free input `LowerClassStepBM`.

* **`LowerClassStepBM n k`**: for all class-equivalent marked ideals `A ≈ B` of the domain in dimension `≤ k`, of maximal
  order, with the same mark and divisor, carriers of the same dimension and agreeing exponents, `LowerClassBM A B` (exactly the
  hypothesis `hLC` of `HironakaG8ClassStep.classFunctorialMaxOrder_stepOneInvBM_of_lowerClass`);
* **`classStepBM_of_lowerClass`**: `LowerClassStepBM n k → ClassStepBM n k`;
* `stepInputsBM_of_lowerClass`, `FamilyInputsLowerBM`, `familyInputsBM_of_lowerClass`, **`exists_bmInvariant_of_lowerClass`**:
  the class-functorial invariants from plan modules 6, 8 and the class data of the lower ideals.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Hironaka.ExtSeqTransport

/-! ### The transport of lane G8C's skeleton of plan module 10 -/

transport_ext_to_seq_module Hironaka.Resolution.HironakaG8ClassStep

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8BFamilyClassStep

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.ResolutionInvariantSeq
  Hironaka.CanonicalCentres Hironaka.HironakaG8BFamily
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree BMInvariant)
open Hironaka.HironakaG8ClassStep (LowerClassBM)

noncomputable section

/-- **The class data of the lower ideals at level `k`** (the hypothesis `hLC` of lane G8C's
`HironakaG8ClassStep.classFunctorialMaxOrder_stepOneInvBM_of_lowerClass`): for two marked ideals `A ≈ B` of the domain in
dimension `≤ k`, of maximal order, `LocWPEquiv`-equivalent, with the same mark and divisor, carriers of the same dimension on
the cosupport and agreeing boundary exponents, the lower ideals of `A` and `B` restricted to every common open of the masks are
`LocWPEquiv`, with carriers of the same dimension and agreeing exponents (Bierstone--Milman 2008, §5 Steps I.A, I.B: the
equivalence class of the lower ideal depends only on that of the marked ideal).  It does not mention a lower invariant. -/
def LowerClassStepBM (n k : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
    IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerClassBM A B

/-- **Plan module 10 from the class data of the lower ideals** (lane G8C's skeleton, transported). -/
theorem classStepBM_of_lowerClass {n k : ℕ} (h : LowerClassStepBM n k) : ClassStepBM n k :=
  fun hn R hR hTI => Seq.HironakaG8ClassStep.classFunctorialMaxOrder_stepOneInvBM_of_lowerClass hn R hR hTI h

/-- **The inputs of the step from plan modules 6, 8 and the class data of the lower ideals.** -/
theorem stepInputsBM_of_lowerClass {n k : ℕ} (h6 : TangentIndepStepBM n k) (h8 : MaxOrderStepBM n k)
    (hLC : LowerClassStepBM n k) : StepInputsBM n k :=
  ⟨h6, h8, classStepBM_of_lowerClass hLC⟩

/-- **The inputs of the family with plan module 10 replaced by the class data of the lower ideals.** -/
def FamilyInputsLowerBM : Prop :=
  ∀ N k : ℕ, k < N → TangentIndepStepBM N (k + 1) ∧ MaxOrderStepBM N (k + 1) ∧ LowerClassStepBM N (k + 1)

theorem familyInputsBM_of_lowerClass (h : FamilyInputsLowerBM) : FamilyInputsBM := fun N k hk =>
  stepInputsBM_of_lowerClass (h N k hk).1 (h N k hk).2.1 (h N k hk).2.2

/-- **Class-functorial resolution invariants from plan modules 6, 8 and the class data of the lower ideals**: for every `N`
there are well-ordered values `Λ` and a resolution invariant in dimension `≤ N` on complex manifolds of dimension `N`, class
functorial for `LocWPEquiv`. -/
theorem exists_bmInvariant_of_lowerClass (h : FamilyInputsLowerBM) :
    ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
      Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ) :=
  exists_bmInvariant (familyInputsBM_of_lowerClass h)

end

end Hironaka.HironakaG8BFamilyClassStep
