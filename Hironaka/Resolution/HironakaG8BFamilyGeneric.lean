import Hironaka.Resolution.HironakaG8BFamily

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The class-functorial induction for an arbitrary Step 1 operator, carrying an arbitrary property of the invariants

Blueprint `hironaka-g8b-family-invariants.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c (module 12).

`HironakaG8BFamily` runs the induction on the dimension for Bierstone--Milman's Step 1 value `stepOneInvBM` of lane G11B's lower
family.  The induction itself does not depend on the Step 1 value: from a class-functorial resolution invariant `R` in dimension
`≤ k` (structure `ResolutionInvariantSeq.ResolutionInvariant`, well-founded values) it needs a value function `S k R` (the Step 1
value) which is a maximal-order value function in dimension `≤ k + 1`, class functorial on the marked ideals of maximal order;
then the general value `genInv (S k R)` is the next invariant.  Some Step 1 values need more of the lower invariant than class
functoriality (lane G11B found that property (4') of `stepOneInvBM R` needs a property of `R` beyond (1)--(7), (4'); inbox I-1370),
so the induction here carries an arbitrary property `Q k inv` of the invariants along: it must hold for the constant invariant
of dimension `0` and pass from `R` to `genInv (S k R)`.

* `ValFn n Λ`, `StepOneOp n` (a Step 1 value for every lower invariant), `InvProp n` (a property of value functions);
* **`StepGood S Q k`**: for every class-functorial lower invariant `R` of index `k` with `Q k R.inv`, `S k R` is a maximal-order
  value function in dimension `≤ k + 1`, class functorial on the marked ideals of maximal order, and `Q (k + 1) (genInv (S k R))`;
* `BMInvariantQ Q k Λ` (a class-functorial invariant with property `Q`), **`generalStepGen`** (the step for any maximal-order
  value function, no further hypothesis), `generalStepQ`, **`invFamilyQ`** (`0 < n`, every `k ≤ n`), `canonicalInvariantQ`,
  **`exists_bmInvariant_gen`**: lane G11C's `ClassFunctorialInvariants` (unfolded) from `Q 0` of the constant invariants and
  `StepGood` at the levels `0, ..., N - 1`;
* `stepGood_of_stepInputsBM`: the inputs of `HironakaG8BFamily` are the instance `S = stepOneInvBM`, `Q = True`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8BFamilyGeneric

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.ResolutionInvariantSeq
  Hironaka.CanonicalCentres
open Hironaka.MaxOrderValue (IsMaxOrderValue)
open Hironaka.GeneralValue (genInv)
open Hironaka.MonomialInvariant (Val)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (ClassFunctorialFor BMInvariant)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)

noncomputable section

variable {n : ℕ}

/-! ### Step 1 operators and properties of invariants -/

section Defs

variable (n) in
/-- Value functions on marked ideals of manifolds of dimension `n` (universe `0`) with values in `Λ`. -/
abbrev ValFn (Λ : Type) :=
  ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ

variable (n) in
/-- **A Step 1 operator**: for every lower invariant of index `k` (structure `ResolutionInvariantSeq.ResolutionInvariant`)
with values in `Λ`, a value function with values in `ℕ ×ₗ WithTop Λ`. -/
abbrev StepOneOp :=
  ∀ (k : ℕ) {Λ : Type} [LinearOrder Λ], ResolutionInvariant.{0, 0} n k Λ → ValFn n (ℕ ×ₗ WithTop Λ)

variable (n) in
/-- **A property of value functions of index `k`** (carried along the induction). -/
abbrev InvProp :=
  ∀ (_k : ℕ) {Λ : Type} [LinearOrder Λ], ValFn n Λ → Prop

/-- **The step works at index `k`** for the Step 1 operator `S` and the property `Q`: for every lower invariant `R` of index `k`,
class functorial for `LocWPEquiv` and with `Q k R.inv`, the Step 1 value `S k R` is a maximal-order value function in dimension
`≤ k + 1`, class functorial on the marked ideals of maximal order, and its general value has `Q (k + 1)`. -/
structure StepGood (S : StepOneOp n) (Q : InvProp n) (k : ℕ) : Prop where
  /-- The three properties of the Step 1 value. -/
  step : ∀ {Λ : Type} [LinearOrder Λ] (R : ResolutionInvariant.{0, 0} n k Λ),
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k R.inv → Q k R.inv →
      IsMaxOrderValue n (k + 1) (S k R) ∧
        ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) (S k R) ∧
        Q (k + 1) (genInv (S k R))

variable (n) in
/-- **A class-functorial resolution invariant with the property `Q`.** -/
structure BMInvariantQ (Q : InvProp n) (k : ℕ) (Λ : Type) [LinearOrder Λ] where
  /-- The class-functorial invariant. -/
  toBMInvariant : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ
  /-- Its property `Q`. -/
  prop : Q k toBMInvariant.toResolutionInvariant.inv

end Defs

/-! ### The step -/

section Step

variable {k : ℕ} {Λ : Type} [LinearOrder Λ]

/-- **The general step for any maximal-order value function** (`0 < n`): if `M` is a maximal-order value function in dimension
`≤ k + 1` (values in `ℕ ×ₗ WithTop Λ`, `Λ` well founded), class functorial on the marked ideals of maximal order, then its general
value is a class-functorial resolution invariant in dimension `≤ k + 1` with well-founded values. -/
def generalStepGen [WellFoundedLT Λ] (M : ValFn n (ℕ ×ₗ WithTop Λ)) (hn : 0 < n) (hM : IsMaxOrderValue n (k + 1) M)
    (hcf : ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) M) :
    BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop Λ))) :=
  haveI := NonmonomialOrderGlobalPhase.wellFoundedLT_genValue (Λ := ℕ ×ₗ WithTop Λ)
  ⟨ofWellFounded n (k + 1) (genInv M) (GeneralStepValue.isInvValue_genInv hM hn),
    HironakaG8P1GenInv.classFunctorial_genInv hM hn hcf⟩

/-- The invariant of the general step is the general value. -/
theorem generalStepGen_inv [WellFoundedLT Λ] (M : ValFn n (ℕ ×ₗ WithTop Λ)) (hn : 0 < n)
    (hM : IsMaxOrderValue n (k + 1) M)
    (hcf : ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k + 1) M) {X : CMfd.{0} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{0} n} (T : BlowupTower X Y) (y : Y) :
    (generalStepGen M hn hM hcf).toResolutionInvariant.inv 𝔪 T y = genInv M 𝔪 T y :=
  rfl

/-- **The general step with the property `Q`** (`0 < n`), from `StepGood S Q k`. -/
def generalStepQ [WellFoundedLT Λ] (S : StepOneOp n) (Q : InvProp n) (R : BMInvariantQ n Q k Λ) (hn : 0 < n)
    (h : StepGood S Q k) :
    BMInvariantQ n Q (k + 1) (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop Λ))) :=
  ⟨generalStepGen (S k R.toBMInvariant.toResolutionInvariant) hn
      (h.step _ R.toBMInvariant.classFunctorial R.prop).1 (h.step _ R.toBMInvariant.classFunctorial R.prop).2.1,
    (h.step _ R.toBMInvariant.classFunctorial R.prop).2.2⟩

end Step

/-! ### The family -/

section Family

/-- **The class-functorial resolution invariants with the property `Q`** (`0 < n`): for every `k ≤ n` an invariant in dimension
`≤ k` with values in `ValTy k`, class functorial for `LocWPEquiv`, with `Q k`; the constant invariant for `k = 0` (given `Q 0` of
it), the general step from `k` to `k + 1` (given `StepGood S Q k` for `k < n`). -/
def invFamilyQ (hn : 0 < n) (S : StepOneOp n) (Q : InvProp n)
    (h0 : Q 0 (ResolutionInvariant.ofDimZero.{0, 0} (n := n) (ValTy 0) (0 : ℕ)).inv)
    (h : ∀ k, k < n → StepGood S Q k) : (k : ℕ) → k ≤ n → BMInvariantQ n Q k (ValTy k)
  | 0, _ => ⟨HironakaG11InvBMClass.BMInvariant.ofDimZero _ (0 : ℕ), h0⟩
  | k + 1, hk => generalStepQ S Q (invFamilyQ hn S Q h0 h k (Nat.le_of_succ_le hk)) hn (h k hk)

/-- The invariant of the family in dimension `≤ k + 1` is the general value of the Step 1 value of the one in dimension `≤ k`. -/
theorem invFamilyQ_succ_inv (hn : 0 < n) (S : StepOneOp n) (Q : InvProp n)
    (h0 : Q 0 (ResolutionInvariant.ofDimZero.{0, 0} (n := n) (ValTy 0) (0 : ℕ)).inv)
    (h : ∀ k, k < n → StepGood S Q k) (k : ℕ) (hk : k + 1 ≤ n) {X : CMfd.{0} n} (𝔪 : MarkedIdeal n X)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (y : Y) :
    (invFamilyQ hn S Q h0 h (k + 1) hk).toBMInvariant.toResolutionInvariant.inv 𝔪 T y =
      genInv (S k (invFamilyQ hn S Q h0 h k (Nat.le_of_succ_le hk)).toBMInvariant.toResolutionInvariant) 𝔪 T y :=
  rfl

variable (n) in
/-- **The class-functorial resolution invariant in dimension `≤ n`** with the property `Q` (`n = 0`: the constant invariant). -/
def canonicalInvariantQ (S : StepOneOp n) (Q : InvProp n)
    (h0 : Q 0 (ResolutionInvariant.ofDimZero.{0, 0} (n := n) (ValTy 0) (0 : ℕ)).inv)
    (h : ∀ k, k < n → StepGood S Q k) : BMInvariantQ n Q n (ValTy n) :=
  match n, S, Q, h0, h with
  | 0, _, _, h0, _ => ⟨HironakaG11InvBMClass.BMInvariant.ofDimZero _ (0 : ℕ), h0⟩
  | m + 1, S, Q, h0, h => invFamilyQ (Nat.succ_pos m) S Q h0 h (m + 1) le_rfl

/-- **Class-functorial resolution invariants exist** (lane G11C's `ClassFunctorialInvariants`, unfolded) for any Step 1
operators `S N` and properties `Q N` such that the constant invariants of dimension `0` have `Q N 0` and the step works at the
indices `k < N`. -/
theorem exists_bmInvariant_gen (S : ∀ N : ℕ, StepOneOp N) (Q : ∀ N : ℕ, InvProp N)
    (h0 : ∀ N : ℕ, Q N 0 (ResolutionInvariant.ofDimZero.{0, 0} (n := N) (ValTy 0) (0 : ℕ)).inv)
    (h : ∀ N k : ℕ, k < N → StepGood (S N) (Q N) k) :
    ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
      Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ) :=
  fun N => ⟨ValTy N, inferInstance, inferInstance,
    ⟨(canonicalInvariantQ N (S N) (Q N) (h0 N) (h N)).toBMInvariant⟩⟩

end Family

/-! ### The instance of `HironakaG8BFamily` -/

section Instance

/-- Bierstone--Milman's Step 1 value (lane G11B's lower family) as a Step 1 operator. -/
def stepOneBM (n : ℕ) : StepOneOp n := fun _ _ _ R {X} 𝔍 {Y} T y =>
  Seq.HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y

/-- The trivial property. -/
def trivProp (n : ℕ) : InvProp n := fun _ _ _ _ => True

/-- **The inputs of `HironakaG8BFamily` at level `k + 1` make the step work** for `stepOneBM` and the trivial property. -/
theorem stepGood_of_stepInputsBM {k : ℕ} (hn : 0 < n) (h : HironakaG8BFamily.StepInputsBM n (k + 1)) :
    StepGood (stepOneBM n) (trivProp n) k where
  step R hR _ :=
    ⟨h.maxOrder R hn (fun 𝔍 hD hmax => h.tangentIndep hn R hR 𝔍 hD hmax),
      h.classStep hn R hR (fun 𝔍 hD hmax => h.tangentIndep hn R hR 𝔍 hD hmax), trivial⟩

end Instance

end

end Hironaka.HironakaG8BFamilyGeneric
