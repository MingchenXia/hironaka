import Hironaka.Resolution.HironakaG8BFamilyGeneric
import Hironaka.Resolution.HironakaG8BFamilyClassStep
import Hironaka.Resolution.HironakaG8ClassStepExp
import Hironaka.Resolution.HironakaG11PresM8Assembly
import Hironaka.Resolution.HironakaG11InvBMPadFamily
import Hironaka.Resolution.HironakaG8BFamilyTangentSeq
import Hironaka.Resolution.HironakaG8TangentExpSucc

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The padded module-12 closing: class-functorial invariants from plan modules 6 and 10 (repair (B'), padded lower family)

Blueprint `hironaka-g11-pres-pad-close.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d (module 12 for the
padded lower family); lane G8B's family-independent induction `HironakaG8BFamilyGeneric`.

With padded lower divisors (lane G11B's decision r7, BPRIME-PLAN §6d) the Step 1 value of a marked ideal `𝔍` evaluates the lower
invariant `R` on the lower ideals with `|𝔍.E|` empty placeholders in front of their divisor:
`𝔍 ↦ stepOneInvBM (padInvSeq R |𝔍.E|) 𝔍` (`padInvSeq`: lane G11B, `HironakaG11InvBMPadInv`).  This module runs the induction on
the dimension (`HironakaG8BFamilyGeneric.exists_bmInvariant_gen`, the trivial carried property) for this Step 1 operator:

* the transport to the structure `ResolutionInvariantSeq.ResolutionInvariant` (`transport_ext_to_seq`, reusing the constants of
  `HironakaG8BFamilySeq` and `HironakaG8BFamilyClassStep`) of plan module 8 for the padded family,
  `HironakaG11PresM8Assembly.isMaxOrderValue_stepOneInvBM_pad` (lane G11C r4): a successful kernel-checked transport shows that it
  uses only properties (1)--(7), (4') of the lower invariants;
* **`stepOnePadBM`**: the padded Step 1 operator;
* **`LowerExpStepBM n k`**: the remaining input of plan module 10 (lane G8C, `HironakaG8ClassStepExp`, hypothesis `hExpB` of
  `classFunctorialMaxOrder_stepOneInvBM_of_belowMark`): the boundary exponents BELOW THE MARK of the lower ideals of two
  class-equivalent marked ideals agree (`R`-free; BM08 Thm 6.1/6.2 with Step I.B); `lowerClassStepBM_of_lowerExp`,
  `classStepBM_of_lowerExp`;
* **`isMaxOrderValue_stepOnePadBM`**: plan module 8 for the padded operator, from plan module 6 (lane G8B's
  `HironakaG8BFamily.TangentIndepStepBM`) applied to the padded invariants (`classFunctorial_padInv`);
* **`classFunctorialMaxOrder_stepOnePadBM`**: plan module 10 for the padded operator (per padding length, then
  `HironakaG11InvBMPadFamily.classFunctorialMaxOrder_lengthFamily`: class-equivalent marked ideals have the same divisor);
* **`stepGood_pad`**, `PadFamilyInputs` (modules 6 and 10 at every level `1 ≤ k ≤ N`, every `N`), **`exists_bmInvariant_pad`**:
  lane G11C's `ClassFunctorialInvariants` (unfolded) from `PadFamilyInputs`;
* with plan module 6 proved by lane G8B (`HironakaG8BFamilyTangentSeq.tangentIndepStepBM_of_expAgreeSucc`, one `R`-free input
  `HironakaG8BFamilyTangent.TangentExpAgreeSuccBM`): **`PadFamilyExpInputs`** (the two `R`-free exponent inputs below the mark,
  modules 6 and 10, at every level), `padFamilyInputs_of_expInputs`, **`exists_bmInvariant_padExp`**;
* with the input of plan module 6 proved by lane G8 (`HironakaG8TangentExpSucc.tangentExpAgreeSuccBM`): **`tangentIndepStepBM`**
  (plan module 6 at every level, unconditionally), **`PadFamilyLowerExpInputs`** (only the input `LowerExpStepBM` of plan module
  10), `padFamilyExpInputs_of_lowerExp`, **`exists_bmInvariant_padLowerExp`**.

The two inputs are statements about EVERY lower invariant (module 6) or about no invariant at all (module 10); neither is
`HironakaG8BFamily.MaxOrderStepBM` / `FamilyInputsBM` (false for the unpadded family) nor `EmptyMemberIndep` (false for `genInv`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Hironaka.ExtSeqTransport

/-! ### The transport of plan module 8 for the padded family -/

transport_ext_to_seq Hironaka.HironakaG11PresM8Assembly.isMaxOrderValue_stepOneInvBM_pad

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11PresPadClose

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.ResolutionInvariantSeq
  Hironaka.CanonicalCentres
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.MaxOrderValue (IsMaxOrderValue)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (ClassFunctorialFor BMInvariant SameCarrierDim ExpAgree)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)
open Hironaka.HironakaG8BFamily (TangentIndepStepBM ClassStepBM)
open Hironaka.HironakaG8BFamilyGeneric (StepOneOp StepGood trivProp exists_bmInvariant_gen)
open Hironaka.HironakaG11InvBMPadInv (padInvSeq padInvSeq_add classFunctorial_padInv)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.HironakaG8ClassStepExp (ExpAgreeBelowMark)

noncomputable section

/-! ### The padded Step 1 operator and the input of plan module 10 -/

section Defs

/-- **The padded Step 1 operator** (BPRIME-PLAN §6d): for a lower invariant `R`, the Step 1 value of `𝔍` is Bierstone--Milman's
Step 1 value formed with the padded lower invariant `padInvSeq R |𝔍.E|` (the lower invariant evaluated on the lower ideals with
`|𝔍.E|` empty members in front of their divisor). -/
def stepOnePadBM (n : ℕ) : StepOneOp n := fun _ _ _ R {X} 𝔍 {Y} T y =>
  Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) (padInvSeq R 𝔍.E.length) 𝔍 (Y := Y) T y

/-- **The remaining input of plan module 10** (lane G8C, `HironakaG8ClassStepExp`: exactly the hypothesis `hExpB` of
`classFunctorialMaxOrder_stepOneInvBM_of_belowMark`, `R`-free): for two marked ideals `A ≈ B` of the domain in dimension `≤ k`,
of maximal order, `LocWPEquiv`-equivalent, with the same mark and divisor, carriers of the same dimension on the cosupport and
agreeing boundary exponents, on every common open of the masks the two restricted lower ideals have the same exponents along
the members of their divisor at the points where the exponent of the first is below the mark (Bierstone--Milman 2008, §5
Step I.B and Theorems 6.1, 6.2: the class of the lower ideal, exponents included, depends only on the class of the marked
ideal; the exponents at or above the mark are proved by lane G8C). -/
def LowerExpStepBM (n k : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
    IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B →
    LowerPairs A B fun {_} P Q => ExpAgreeBelowMark P Q

/-- **The class data of the lower ideals from their exponents below the mark** (lane G8C's `lowerClassBM_of_exp` and
`lowerPairs_expAgree_of_belowMark`). -/
theorem lowerClassStepBM_of_lowerExp {n k : ℕ} (hn : 0 < n) (h : LowerExpStepBM n k) :
    HironakaG8BFamilyClassStep.LowerClassStepBM n k :=
  HironakaG8ClassStepDim.lowerClassBM_of_exp hn fun A B hA hB hmA hmB hAB hd hE hdim h0 =>
    HironakaG8ClassStepExp.lowerPairs_expAgree_of_belowMark hn hA hB hmA hmB hAB hd hE hdim
      (h A B hA hB hmA hmB hAB hd hE hdim h0)

/-- **Plan module 10 (lane G8B's input `ClassStepBM`) from the exponents below the mark.** -/
theorem classStepBM_of_lowerExp {n k : ℕ} (hn : 0 < n) (h : LowerExpStepBM n k) : ClassStepBM n k :=
  HironakaG8BFamilyClassStep.classStepBM_of_lowerClass (lowerClassStepBM_of_lowerExp hn h)

end Defs

/-! ### The step for the padded operator -/

section Step

variable {n k : ℕ}

/-- **Plan module 8 for the padded Step 1 operator** (`0 < n`): for a class-functorial lower invariant `R` of index `k`, the padded
Step 1 value is a maximal-order value function in dimension `≤ k + 1`, given plan module 6 at level `k + 1` (applied to the padded
invariants `padInvSeq R m`, class functorial by `classFunctorial_padInv`); the padding law is `padInvSeq_add`. -/
theorem isMaxOrderValue_stepOnePadBM (hn : 0 < n) (h6 : TangentIndepStepBM n (k + 1)) {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariant.{0, 0} n k Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k R.inv) :
    IsMaxOrderValue n (k + 1) (stepOnePadBM n k R) :=
  Seq.HironakaG11PresM8Assembly.isMaxOrderValue_stepOneInvBM_pad (k := k + 1) (padInvSeq R) hn (padInvSeq_add R)
    fun 𝔍 hD hmax => h6 hn (padInvSeq R 𝔍.E.length) (classFunctorial_padInv R _ hR) 𝔍 hD hmax

/-- **Plan module 10 for the padded Step 1 operator** (`0 < n`): the padded Step 1 value of a class-functorial lower invariant is
class functorial on the marked ideals of maximal order, given plan module 6 and the input `LowerExpStepBM` of plan module 10 at
level `k + 1` (for each padding length, then `classFunctorialMaxOrder_lengthFamily`). -/
theorem classFunctorialMaxOrder_stepOnePadBM (hn : 0 < n) (h6 : TangentIndepStepBM n (k + 1))
    (h10 : LowerExpStepBM n (k + 1)) {Λ : Type} [LinearOrder Λ] (R : ResolutionInvariant.{0, 0} n k Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k R.inv) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) (stepOnePadBM n k R) :=
  HironakaG11InvBMPadFamily.classFunctorialMaxOrder_lengthFamily
    (fun m {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) (padInvSeq R m) 𝔍 (Y := Y) T y)
    fun m => classStepBM_of_lowerExp hn h10 hn (padInvSeq R m) (classFunctorial_padInv R m hR)
      fun 𝔍 hD hmax => h6 hn (padInvSeq R m) (classFunctorial_padInv R m hR) 𝔍 hD hmax

/-- **The step works for the padded operator** (`0 < n`), given plan modules 6 and 10 at level `k + 1`. -/
theorem stepGood_pad (hn : 0 < n) (h6 : TangentIndepStepBM n (k + 1)) (h10 : LowerExpStepBM n (k + 1)) :
    StepGood (stepOnePadBM n) (trivProp n) k where
  step R hR _ :=
    ⟨isMaxOrderValue_stepOnePadBM hn h6 R hR, classFunctorialMaxOrder_stepOnePadBM hn h6 h10 R hR, trivial⟩

end Step

/-! ### The family -/

section Family

/-- **The inputs of the padded family**: plan module 6 (lane G8B's `TangentIndepStepBM`) and the input of plan module 10
(`LowerExpStepBM`) at every level `1 ≤ k ≤ N`, for every ambient dimension `N`. -/
def PadFamilyInputs : Prop :=
  ∀ N k : ℕ, k < N → TangentIndepStepBM N (k + 1) ∧ LowerExpStepBM N (k + 1)

/-- **Class-functorial resolution invariants exist, given the inputs of the padded family**: for every `N` there are
well-ordered values `Λ` and a resolution invariant in dimension `≤ N` on complex manifolds of dimension `N`, class functorial for
`LocWPEquiv` (lane G11C's `ClassFunctorialInvariants`, unfolded). -/
theorem exists_bmInvariant_pad (h : PadFamilyInputs) :
    ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
      Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ) :=
  exists_bmInvariant_gen stepOnePadBM trivProp (fun _ => trivial) fun N k hk =>
    stepGood_pad (Nat.zero_lt_of_lt hk) (h N k hk).1 (h N k hk).2

/-- **The `R`-free inputs of the padded family** (plan module 6 being proved by lane G8B from its exponent input): at every level
`1 ≤ k ≤ N`, for every ambient dimension `N`, (i) lane G8B's `TangentExpAgreeSuccBM` (for one marked ideal of maximal order and
two hypersurfaces of maximal contact, the level-`(s+1)` lower ideals have the same boundary exponents below the mark) and (ii)
`LowerExpStepBM` (for two class-equivalent marked ideals, the lower ideals have the same boundary exponents below the mark).
Neither mentions a resolution invariant. -/
def PadFamilyExpInputs : Prop :=
  ∀ N k : ℕ, k < N → HironakaG8BFamilyTangent.TangentExpAgreeSuccBM N (k + 1) ∧ LowerExpStepBM N (k + 1)

/-- **The inputs of the padded family from the two exponent inputs** (plan module 6: lane G8B's
`tangentIndepStepBM_of_expAgreeSucc`). -/
theorem padFamilyInputs_of_expInputs (h : PadFamilyExpInputs) : PadFamilyInputs := fun N k hk =>
  ⟨HironakaG8BFamilyTangentSeq.tangentIndepStepBM_of_expAgreeSucc (h N k hk).1, (h N k hk).2⟩

/-- **Class-functorial resolution invariants exist, given the two `R`-free exponent inputs below the mark** (lane G11C's
`ClassFunctorialInvariants`, unfolded). -/
theorem exists_bmInvariant_padExp (h : PadFamilyExpInputs) :
    ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
      Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ) :=
  exists_bmInvariant_pad (padFamilyInputs_of_expInputs h)

/-- **Plan module 6 holds** (at every level, for every class-functorial lower invariant): lane G8B's
`tangentIndepStepBM_of_expAgreeSucc` with its input proved by lane G8 (`tangentExpAgreeSuccBM`). -/
theorem tangentIndepStepBM (n k : ℕ) : TangentIndepStepBM n k :=
  HironakaG8BFamilyTangentSeq.tangentIndepStepBM_of_expAgreeSucc (HironakaG8TangentExpSucc.tangentExpAgreeSuccBM n k)

/-- **The input of the padded family** with plan module 6 proved: the input `LowerExpStepBM` of plan module 10 (for two
class-equivalent marked ideals the lower ideals have the same boundary exponents below the mark) at every level `1 ≤ k ≤ N`, for
every ambient dimension `N`.  It does not mention a resolution invariant. -/
def PadFamilyLowerExpInputs : Prop :=
  ∀ N k : ℕ, k < N → LowerExpStepBM N (k + 1)

/-- The two exponent inputs from the input of plan module 10 (the input of plan module 6 being proved). -/
theorem padFamilyExpInputs_of_lowerExp (h : PadFamilyLowerExpInputs) : PadFamilyExpInputs := fun N k hk =>
  ⟨HironakaG8TangentExpSucc.tangentExpAgreeSuccBM N (k + 1), h N k hk⟩

/-- **Class-functorial resolution invariants exist, given the input of plan module 10 alone** (the boundary exponents below the
mark of the lower ideals of class-equivalent marked ideals agree; lane G11C's `ClassFunctorialInvariants`, unfolded). -/
theorem exists_bmInvariant_padLowerExp (h : PadFamilyLowerExpInputs) :
    ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
      Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ) :=
  exists_bmInvariant_padExp (padFamilyExpInputs_of_lowerExp h)

end Family

end

end Hironaka.HironakaG11PresPadClose
