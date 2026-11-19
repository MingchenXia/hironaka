import Hironaka.Resolution.HironakaG8BFamilySeq
import Hironaka.Resolution.HironakaG8P1GenInv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The class-functorial resolution invariants of repair (B'): induction on the dimension

Blueprint `hironaka-g8b-family-invariants.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 module 12 and §6c, "Modules
10--13 against lane G11C's target".  Human decision on I-1304: repair (B') -- Bierstone--Milman's lower family on the generic
Step 1 skeleton, with class functoriality carried through the induction on the dimension (Bierstone--Milman 2008, Theorem 7.1:
"strong functorial desingularization in lower dimension"; §5 Step I.A).

The induction of `CanonicalCentres.invFamily`, with Bierstone--Milman's Step 1 value `stepOneInvBM` (lane G11B) in place of
Włodarczyk's and with class functoriality (`HironakaG11InvBMClass.ClassFunctorialFor`, for lane G8's local equivalence
`LocWPEquiv`) carried along.  One step from a class-functorial invariant `R` in dimension `≤ k` (well-founded values) to one in
dimension `≤ k + 1`:

* the value is the general value `GeneralValue.genInv M` of `M = stepOneInvBM R`; it has properties (1)--(7), (4')
  (`GeneralStepValue.isInvValue_genInv`) once `M` is a maximal-order value function, and property (8') because its values are
  well founded (`CanonicalCentres.ofWellFounded`);
* it is class functorial (`HironakaG8P1GenInv.classFunctorial_genInv`, plan module 11) once `M` is class functorial on the
  marked ideals of maximal order.

The three facts about `stepOneInvBM R` that the step needs are the outputs of plan modules 6, 8 and 10 (lanes G11B and G8C), not
yet in the library.  They enter as the hypotheses `TangentIndepStepBM`, `MaxOrderStepBM`, `ClassStepBM` (bundled in
`StepInputsBM`), each the transport (`HironakaG8BFamilySeq`) to `ResolutionInvariantSeq.ResolutionInvariant` of the announced
statement of its module:

* module 6, `tangentIndepBM_of_classFunctorial` (BPRIME-PLAN §6c): a class-functorial lower invariant has the independence of
  the hypersurface of maximal contact (`TangentIndepBM`, BM08 §5 Step I.A, Cor 4.2);
* module 8, `isMaxOrderValue_stepOneInvBM` (BPRIME-PLAN §6c): given that independence, `stepOneInvBM R` is a value function for
  the marked ideals of maximal order (`MaxOrderValue.IsMaxOrderValue`);
* module 10, `classFunctorialMaxOrder_stepOneInvBM` (inbox I-1361): given both, `stepOneInvBM R` is class functorial on the
  marked ideals of maximal order (`HironakaG8P1GenInv.ClassFunctorialMaxOrderFor`).

They are statements about every lower invariant (not about the invariant built here), they are theorems of Bierstone--Milman
2008 (§§4--7), and none mentions class functoriality in dimension `≤ k + 1` or the existence of invariants.

## Main results

* **`generalStepBM`**: the step, from `R : BMInvariant n LocWPEquiv k Λ` and the two facts `IsMaxOrderValue`,
  `ClassFunctorialMaxOrderFor` about `stepOneInvBM R` (no hypothesis beyond these); `generalStepBM_inv`;
* `generalStepBMOf`: the step from the inputs `StepInputsBM n (k + 1)`;
* **`invFamilyBM`**: for `0 < n`, a class-functorial resolution invariant in dimension `≤ k` with values in
  `CanonicalCentres.ValTy k` for every `k ≤ n`, by induction (`BMInvariant.ofDimZero` for `k = 0`); `invFamilyBMAll` for all `k`
  (inputs at every level);
* **`canonicalInvariantBM n`**: one in dimension `≤ n` (`n = 0`: `ofDimZero`);
* **`exists_bmInvariant`**: for every `N` there are well-ordered values `Λ` and an invariant in
  `BMInvariant N LocWPEquiv N Λ` (the proposition `Hironaka.Analytic.Unibranch.HironakaG11PresReduction.ClassFunctorialInvariants`, lane
  G11C's target), given `FamilyInputsBM`.

**SUPERSEDED in part (inbox I-1370 C-0002, same round).**  Lane G11B found that property (4') of `stepOneInvBM R` compares
the lower ideal of `𝔍` formed after an empty-centred prefix `P` (whose divisor has the `|P|` empty members born along `P` in
FRONT) with that of `𝔍_P`; the general value `genInv` sees such members (its monomial entry records ABSOLUTE positions:
`MonomialInvariantEmptyMember.genInv_insertEmpty_of_nmOrd_eq_zero`, `shiftVal_ne_self`).  So for the lower invariants of the
family at index `≥ 1` property (4') of `stepOneInvBM R` is very likely false, and with it the input `MaxOrderStepBM` (hence
`FamilyInputsBM`) for the CURRENT lower family.  The induction itself is unaffected: `HironakaG8BFamilyGeneric` runs it for an
arbitrary Step 1 operator (and an arbitrary property carried along), to be instantiated with the corrected family.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG8BFamily

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.ResolutionInvariantSeq
  Hironaka.CanonicalCentres
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.MaxOrderValue (IsMaxOrderValue)
open Hironaka.GeneralValue (genInv)
open Hironaka.MonomialInvariant (Val)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (ClassFunctorialFor BMInvariant)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)

noncomputable section

/-! ### The inputs: the outputs of plan modules 6, 8, 10 for lower invariants of the new structure -/

section Inputs

/-- **Plan module 6** (BPRIME-PLAN §6c, `tangentIndepBM_of_classFunctorial`, transported to the new structure): for `0 < n`, a
lower invariant in dimension `≤ k - 1` that is class functorial for `LocWPEquiv` has, for every marked ideal of the domain in
dimension `≤ k` of maximal order, the independence of the hypersurface of maximal contact (`TangentIndepBM`; Bierstone--Milman
2008, §5 Step I.A, Cor 4.2: the coefficient ideals on two hypersurfaces of maximal contact are equivalent, so a class-functorial
invariant takes the same values on them). -/
def TangentIndepStepBM (n k : ℕ) : Prop :=
  ∀ {Λ : Type} [LinearOrder Λ], 0 < n → ∀ (R : ResolutionInvariant.{0, 0} n (k - 1) Λ),
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv →
    ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      Seq.HironakaG11InvBMTangentIndep.TangentIndepBM (k := k) 𝔍 R

/-- (SUPERSEDED, see the module documentation: very likely false for the current lower family at `k ≥ 2`.)
**Plan module 8** (BPRIME-PLAN §6c, `isMaxOrderValue_stepOneInvBM`, transported to the new structure): for `0 < n` and a
lower invariant `R` in dimension `≤ k - 1` with the independence of the hypersurface of maximal contact for the marked ideals of
the domain of maximal order, Bierstone--Milman's Step 1 value `stepOneInvBM R` has properties (1)--(7), (4') on the marked ideals
of maximal order in dimension `≤ k` (Bierstone--Milman 2008, §5 Step I, §7.2). -/
def MaxOrderStepBM (n k : ℕ) : Prop :=
  ∀ {Λ : Type} [LinearOrder Λ] (R : ResolutionInvariant.{0, 0} n (k - 1) Λ), 0 < n →
    (∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      Seq.HironakaG11InvBMTangentIndep.TangentIndepBM (k := k) 𝔍 R) →
    IsMaxOrderValue n k
      (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y)

/-- **Plan module 10** (inbox I-1361, `classFunctorialMaxOrder_stepOneInvBM`, transported to the new structure): for `0 < n`
and a lower invariant `R` in dimension `≤ k - 1`, class functorial for `LocWPEquiv` and with the independence of the
hypersurface of maximal contact, Bierstone--Milman's Step 1 value `stepOneInvBM R` is class functorial for `LocWPEquiv` on the
marked ideals of maximal order in dimension `≤ k` (Bierstone--Milman 2008, §5 Steps I.A, I.B: the lower ideals of equivalent
marked ideals are equivalent). -/
def ClassStepBM (n k : ℕ) : Prop :=
  ∀ {Λ : Type} [LinearOrder Λ], 0 < n → ∀ (R : ResolutionInvariant.{0, 0} n (k - 1) Λ),
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv →
    (∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      Seq.HironakaG11InvBMTangentIndep.TangentIndepBM (k := k) 𝔍 R) →
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y)

/-- **The inputs of the step to dimension `≤ k`**: plan modules 6, 8 and 10 at level `k`. -/
structure StepInputsBM (n k : ℕ) : Prop where
  /-- Plan module 6. -/
  tangentIndep : TangentIndepStepBM n k
  /-- Plan module 8. -/
  maxOrder : MaxOrderStepBM n k
  /-- Plan module 10. -/
  classStep : ClassStepBM n k

/-- **The inputs of the whole family**: the step inputs at every level `1 ≤ k ≤ N`, for every ambient dimension `N`.
(SUPERSEDED: contains `MaxOrderStepBM`, very likely false for the current lower family; see the module documentation.) -/
def FamilyInputsBM : Prop :=
  ∀ N k : ℕ, k < N → StepInputsBM N (k + 1)

end Inputs

/-! ### The step -/

section Step

variable {n k : ℕ} {Λ : Type} [LinearOrder Λ]

/-- **The general step of repair (B')** (`0 < n`): from a class-functorial resolution invariant `R` in dimension `≤ k` with
well-founded values, the general value of Bierstone--Milman's Step 1 value of `R` is a class-functorial resolution invariant in
dimension `≤ k + 1`, provided `stepOneInvBM R` is a maximal-order value function (`hM`) that is class functorial on the marked
ideals of maximal order (`hcf`). -/
def generalStepBM [WellFoundedLT Λ] (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ) (hn : 0 < n)
    (hM : IsMaxOrderValue n (k + 1)
      (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R.toResolutionInvariant 𝔍 (Y := Y) T y))
    (hcf : ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1)
      (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R.toResolutionInvariant 𝔍 (Y := Y) T y)) :
    BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop Λ))) :=
  haveI := NonmonomialOrderGlobalPhase.wellFoundedLT_genValue (Λ := ℕ ×ₗ WithTop Λ)
  ⟨ofWellFounded n (k + 1)
      (genInv fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R.toResolutionInvariant 𝔍 (Y := Y) T y)
      (GeneralStepValue.isInvValue_genInv hM hn),
    HironakaG8P1GenInv.classFunctorial_genInv hM hn hcf⟩

/-- The invariant of the general step is the general value of Bierstone--Milman's Step 1 value. -/
theorem generalStepBM_inv [WellFoundedLT Λ] (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ)
    (hn : 0 < n)
    (hM : IsMaxOrderValue n (k + 1)
      (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R.toResolutionInvariant 𝔍 (Y := Y) T y))
    (hcf : ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1)
      (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R.toResolutionInvariant 𝔍 (Y := Y) T y))
    {X : CMfd.{0} n} (𝔪 : MarkedIdeal n X) {Y : CMfd.{0} n} (T : BlowupTower X Y) (y : Y) :
    (generalStepBM R hn hM hcf).toResolutionInvariant.inv 𝔪 T y =
      genInv (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R.toResolutionInvariant 𝔍 (Y := Y) T y)
        𝔪 T y :=
  rfl

/-- The independence of the hypersurface of maximal contact for the lower invariant of a step (plan module 6). -/
theorem tangentIndep_of_stepInputs (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ) (hn : 0 < n)
    (h : StepInputsBM n (k + 1)) {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X) (hD : IsInvDomain (k + 1) 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) :
    Seq.HironakaG11InvBMTangentIndep.TangentIndepBM (k := k + 1) 𝔍 R.toResolutionInvariant :=
  h.tangentIndep hn R.toResolutionInvariant R.classFunctorial 𝔍 hD hmax

/-- **The general step from the inputs** at level `k + 1` (plan modules 6, 8, 10). -/
def generalStepBMOf [WellFoundedLT Λ] (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ) (hn : 0 < n)
    (h : StepInputsBM n (k + 1)) :
    BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop Λ))) :=
  generalStepBM R hn (h.maxOrder R.toResolutionInvariant hn (tangentIndep_of_stepInputs R hn h))
    (h.classStep hn R.toResolutionInvariant R.classFunctorial (tangentIndep_of_stepInputs R hn h))

end Step

/-! ### The family -/

section Family

variable {n : ℕ}

/-- **The class-functorial resolution invariants of repair (B')** (`0 < n`): for every `k ≤ n`, a class-functorial resolution
invariant in dimension `≤ k` on complex manifolds of dimension `n`, with values in `ValTy k`; `ofDimZero` for `k = 0`, the
general step `generalStepBMOf` from `k` to `k + 1` (inputs at the levels `1, ..., n`). -/
def invFamilyBM (hn : 0 < n) (h : ∀ k, k < n → StepInputsBM n (k + 1)) :
    (k : ℕ) → k ≤ n → BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k (ValTy k)
  | 0, _ => BMInvariant.ofDimZero _ (0 : ℕ)
  | k + 1, hk => generalStepBMOf (invFamilyBM hn h k (Nat.le_of_succ_le hk)) hn (h k hk)

/-- The invariant in dimension `≤ k + 1` is the general step of the one in dimension `≤ k`. -/
theorem invFamilyBM_succ (hn : 0 < n) (h : ∀ k, k < n → StepInputsBM n (k + 1)) (k : ℕ) (hk : k + 1 ≤ n) :
    invFamilyBM hn h (k + 1) hk = generalStepBMOf (invFamilyBM hn h k (Nat.le_of_succ_le hk)) hn (h k hk) :=
  rfl

/-- The invariant of the family in dimension `≤ k + 1` is the general value of Bierstone--Milman's Step 1 value of the one in
dimension `≤ k`. -/
theorem invFamilyBM_succ_inv (hn : 0 < n) (h : ∀ k, k < n → StepInputsBM n (k + 1)) (k : ℕ) (hk : k + 1 ≤ n)
    {X : CMfd.{0} n} (𝔪 : MarkedIdeal n X) {Y : CMfd.{0} n} (T : BlowupTower X Y) (y : Y) :
    (invFamilyBM hn h (k + 1) hk).toResolutionInvariant.inv 𝔪 T y =
      genInv (fun {X} 𝔍 {Y} T y => Seq.HironakaG11InvBMLower.stepOneInvBM (X := X)
        (invFamilyBM hn h k (Nat.le_of_succ_le hk)).toResolutionInvariant 𝔍 (Y := Y) T y) 𝔪 T y :=
  rfl

/-- **The family at every level** (inputs at every level). -/
def invFamilyBMAll (hn : 0 < n) (h : ∀ k, StepInputsBM n (k + 1)) :
    (k : ℕ) → BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k (ValTy k)
  | 0 => BMInvariant.ofDimZero _ (0 : ℕ)
  | k + 1 => generalStepBMOf (invFamilyBMAll hn h k) hn (h k)

variable (n) in
/-- **The class-functorial resolution invariant in dimension `≤ n`** on complex manifolds of dimension `n` (repair (B')):
`invFamilyBM` at `k = n` for `0 < n`, `ofDimZero` for `n = 0`. -/
def canonicalInvariantBM (h : ∀ k, k < n → StepInputsBM n (k + 1)) :
    BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) n (ValTy n) :=
  match n, h with
  | 0, _ => BMInvariant.ofDimZero _ (0 : ℕ)
  | m + 1, h => invFamilyBM (Nat.succ_pos m) h (m + 1) le_rfl

/-- **Class-functorial resolution invariants exist** (lane G11C's target `ClassFunctorialInvariants`, given the inputs of plan
modules 6, 8, 10): for every `N` a resolution invariant in dimension `≤ N` on complex manifolds of dimension `N`, with
well-ordered values, class functorial for `LocWPEquiv`. -/
theorem exists_bmInvariant (h : FamilyInputsBM) :
    ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
      Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ) :=
  fun N => ⟨ValTy N, inferInstance, inferInstance, ⟨canonicalInvariantBM N (h N)⟩⟩

end Family

end

end Hironaka.HironakaG8BFamily
