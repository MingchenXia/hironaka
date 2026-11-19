/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Data
public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.Stage.Mono
import Hironaka.Scheme.BlowUpSequence.FunctorRestrict
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Congruence of Lemma 102 and Theorem 103 in the dimension bound

The constructions of Lemma 102 and Theorem 103 (`Hironaka.BoundaryClearing`,
`Hironaka.OrderReduction`) read the dimension bound `n` ONLY through the class proofs and through
the choice of the inductive input applied — never as data. So two instances of the same
construction, at stages `n` and `n' ≤ n`, fed inductive inputs that AGREE on the marked triples of
dimension `≤ n' − 1` (where both are evaluated), take the same value at every triple of the smaller
class. This module proves the congruences on VALUES, heterogeneous in the stage (both class proofs
are arguments):

* `Hironaka.BD.bdData_congr` — the data of [Kol07, Lemma 102]: at mark `0` both functors are
  `zeroFunctor` (no inductive input); at mark `m + 1` both are `dataFunctor`, which evaluates the
  input ONCE, at the restricted marked triple of dimension `≤ n' − 1` (`rawSeq`), where the
  agreement hypothesis applies.
* `Hironaka.BO.step21Seq_congr`, `step22Functor_congr`, `step2Seq_congr`, `maxContactCase_congr` —
  Step 2 of the proof of [Kol07, Theorem 103] (the maximal contact case, [Kol07, 104]), by induction
  along the Step 2.1 recursion and the case split of the re-tuned Step 2.2, the dependent Step 2.2
  input triple handled by generalising over the Step 2.1 sequence.
* `Hironaka.BO.functor_congr` — Theorem 103 itself: `BO_{n,m}` is the globalization of the local
  functor along local covers (`OrderSeqAssignment.globalize`, never unfolded); RESTRICTED to the
  stage-`n'` class (`OrderSeqAssignment.restrict`), the stage-`n` functor agrees with the stage-`n'`
  local functor on the local triples (`functor_seq_localClass` at stage `n` through
  `Triple.boClass_mono`, then `maxContactCase_congr`) and commutes with surjective open-immersion
  coproducts, so the uniqueness of the extension in [Kol07, Theorem 105] (`globalization_unique`)
  identifies it with the stage-`n'` functor.
* `Hironaka.BO.data_congr` — Theorem 103 as data (`BO.data`) at `bdData`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.BD

/-- Congruence of the data of [Kol07, Lemma 102] in the dimension bound: `bdData` at stages `n` and
`n' ≤ n`, from inductive inputs that agree on the marked triples of dimension `≤ n' − 1`, take the
same value at a triple of both classes. At mark `0` both functors are `zeroFunctor` (no input); at
mark `m + 1` both are `dataFunctor`, `nil` below the mark and at the mark `rawSeq` with the input
evaluated ONCE, at the restricted marked triple — of dimension `≤ n' − 1` by
`hasDimLE_restrictedTriple` at stage `n'`. -/
theorem bdData_congr {n n' m j : ℕ}
    (Dom Dom' : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (B' : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom' k))
    (hDom : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hDom' : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n' - 1) → T'.m = tuningParam m → Dom' k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hB' : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom' k T'),
      ((B' k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hsm' : ∀ (k : Type u) [Field k] [CharZero k], (B' k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hbc' : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B' k).CommutesWithBaseChange (B' L) σ)
    (hagree : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (h₁ : Dom k T')
      (h₂ : Dom' k T'), T'.toTriple.HasDimLE (n' - 1) → (B k).seq T' h₁ = (B' k).seq T' h₂)
    (k : Type u) [Field k] [CharZero k] (T : Triple k) (hT : T.BDClass n m j)
    (hT' : T.BDClass n' m j) :
    ((bdData n m j Dom B hDom hB hsm hbc).functor k).seq T hT =
      ((bdData n' m j Dom' B' hDom' hB' hsm' hbc').functor k).seq T hT' := by
  cases m with
  | zero =>
    change (zeroFunctor n j).seq T hT = (zeroFunctor n' j).seq T hT'
    rw [zeroFunctor_seq, zeroFunctor_seq]
  | succ m =>
    change (dataFunctor n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom k)).seq T hT =
      (dataFunctor n' (m + 1) j (Nat.le_add_left 1 m) (B' k) (hDom' k)).seq T hT'
    by_cases h : T.I.maxOrd = ((m + 1 : ℕ) : ℕ∞)
    · rw [dataFunctor_seq_of_maxOrd_eq n (m + 1) j _ (B k) (hDom k) T hT h,
        dataFunctor_seq_of_maxOrd_eq n' (m + 1) j _ (B' k) (hDom' k) T hT' h, functor_seq,
        functor_seq]
      refine congrArg BlowUpSequence.eraseEmpty ?_
      unfold rawSeq rawSeqD
      have hd := domain_tuned (Nat.le_add_left 1 m) hT' h
      exact congrArg (fun S => BlowUpSequence.pushforward (BlowUpSequence.cons _ _ S) _)
        (hagree k _ _ _ (hasDimLE_restrictedTriple _ _ _ hd.2.1 hd.2.2.1 hd.1))
    · have hlt : T.I.maxOrd < ((m + 1 : ℕ) : ℕ∞) := lt_of_le_of_ne hT.2.1 h
      rw [dataFunctor_seq_of_maxOrd_lt n (m + 1) j _ (B k) (hDom k) T hT hlt,
        dataFunctor_seq_of_maxOrd_lt n' (m + 1) j _ (B' k) (hDom' k) T hT' hlt]

end Hironaka.BD

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n n' : ℕ}

section Step21

variable {m : ℕ} (T : Triple k)

/-- Congruence of Step 2.1 of [Kol07, 104] in the dimension bound: the Step 2.1 states at stages `n`
and `n' ≤ n`, from Lemma 102 data that agree pointwise on the triples of both classes, coincide (as
carried sequences) — by induction on the number of rounds: the round at a position of `E` is the
datum's value at the induced triple, equal by `hbd`; beyond the last position both states are
unchanged. -/
theorem step21Seq_congr (hn : T.HasDimLE n) (hn' : T.HasDimLE n') (hmax : T.I.maxOrd ≤ m)
    (bd : ∀ j : ℕ, BDData.{u} n m j) (bd' : ∀ j : ℕ, BDData.{u} n' m j)
    (hbd : ∀ (j : ℕ) (T₀ : Triple k) (h₁ : Triple.BDClass n m j T₀)
      (h₂ : Triple.BDClass n' m j T₀),
      ((bd j).functor k).seq T₀ h₁ = ((bd' j).functor k).seq T₀ h₂) (j : ℕ) :
    step21Seq T hn hmax bd j = step21Seq T hn' hmax bd' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    apply Subtype.ext
    by_cases hj : j < Fintype.card T.E.ι
    · rw [step21Seq_succ_of_lt T hn hmax bd j hj, step21Seq_succ_of_lt T hn' hmax bd' j hj, ← ih]
      exact congrArg _ (hbd j _ _ _)
    · rw [step21Seq_succ_of_not_lt T hn hmax bd j hj, step21Seq_succ_of_not_lt T hn' hmax bd' j hj,
        ih]

end Step21

section Step22

variable (bd : ∀ m j : ℕ, BDData.{u} n m j) (bd' : ∀ m j : ℕ, BDData.{u} n' m j)
  (hbd : ∀ (m j : ℕ) (T₀ : Triple k) (h₁ : Triple.BDClass n m j T₀)
    (h₂ : Triple.BDClass n' m j T₀),
    ((bd m j).functor k).seq T₀ h₁ = ((bd' m j).functor k).seq T₀ h₂)

include hbd in
/-- Congruence of Step 2.2 of [Kol07, 104] in the dimension bound: the re-tuned Lemma 102
(`step22Functor`) at stages `n` and `n' ≤ n` takes the same value at a triple of both classes — at
the mark both are the datum at `s(m)` on the tuned triple (`hbd`), below it both are `nil`. -/
theorem step22Functor_congr (m j : ℕ) (hm : 1 ≤ m) (T₀ : Triple k) (hT₀ : Triple.BDClass n m j T₀)
    (hT₀' : Triple.BDClass n' m j T₀) :
    (step22Functor bd m j hm).seq T₀ hT₀ = (step22Functor bd' m j hm).seq T₀ hT₀' := by
  by_cases h : T₀.I.maxOrd = m
  · rw [step22Functor_seq_of_maxOrd_eq bd m j hm T₀ hT₀ h,
      step22Functor_seq_of_maxOrd_eq bd' m j hm T₀ hT₀' h]
    exact hbd (tuningParam m) j _ _ _
  · have hlt : T₀.I.maxOrd < m := lt_of_le_of_ne hT₀.2.1 h
    rw [step22Functor_seq_of_maxOrd_lt bd m j hm T₀ hT₀ hlt,
      step22Functor_seq_of_maxOrd_lt bd' m j hm T₀ hT₀' hlt]

variable {m : ℕ} (T : Triple k) (hn : T.HasDimLE n) (hmax : T.I.maxOrd ≤ m) (hm : 1 ≤ m)
  {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

include hbd in
/-- Step 2 at stage `n'`, generalised over its Step 2.1 sequence `S₂` with `S₂` equal to the Step
2.1 sequence at stage `n` (the dependent Step 2.2 input triple is handled by this generalisation):
it is Step 2 at stage `n`. -/
theorem step2Seq_congr_aux (S₂ : BlowUpSequence T.X.left)
    (hS₂ : S₂.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (e₁ : S₂ = (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1)
    (hsnc₂ : ((S₂.exceptionalFamily T.E).append (S₂.strictTransformSeq H (Fin.last _))).IsSnc)
    (j' : ℕ) (hj' : j' = Fintype.card (S₂.exceptionalFamily T.E).ι)
    (hT₂' : Triple.BDClass n' m j' (step22TripleOfSeq T S₂ hS₂ hsnc₂)) :
    S₂.concat ((step22Functor bd' m j' hm).seq (step22TripleOfSeq T S₂ hS₂ hsnc₂) hT₂') =
      step2Seq T hn hmax bd hm hH hle := by
  subst e₁ hj'
  exact (congrArg _ (step22Functor_congr bd bd' hbd m _ hm _
    (bdClass_step22Triple T hn hmax bd hm hH hle) hT₂')).symm

include hbd in
/-- Congruence of Step 2 of the proof of [Kol07, Theorem 103] in the dimension bound: Step 2 for a
smooth hypersurface of maximal contact, at stages `n` and `n' ≤ n` with pointwise agreeing Lemma 102
data, coincide — Step 2.1 by `step21Seq_congr`, Step 2.2 on the (then equal) input triple by
`step22Functor_congr`. -/
theorem step2Seq_congr (hn' : T.HasDimLE n') :
    step2Seq T hn hmax bd hm hH hle = step2Seq T hn' hmax bd' hm hH hle := by
  have e₁ : (step21Seq T hn' hmax (bd' m) (Fintype.card T.E.ι)).1 =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1 :=
    congrArg Subtype.val (step21Seq_congr T hn' hn hmax (bd' m) (bd m)
      (fun j T₀ h₁ h₂ => (hbd m j T₀ h₂ h₁).symm) _)
  exact (step2Seq_congr_aux bd bd' hbd T hn hmax hm hH hle _
    (isOrderSeq_step21Seq T hn' hmax (bd' m) _) e₁
    (step22Triple T hn' hmax bd' hm hH hle).isSnc _ rfl
    (bdClass_step22Triple T hn' hmax bd' hm hH hle)).symm

include hbd in
/-- Congruence of Steps 1–2 of the proof of [Kol07, Theorem 103] in the dimension bound: the
maximal-contact case `BO^H_{n,m}` at stages `n` and `n' ≤ n`, with pointwise agreeing Lemma 102
data, coincide — at the mark by `step2Seq_congr` on the tuned triple, below it both are `nil`. -/
theorem maxContactCase_congr (hT : Triple.BOClass n m T) (hT' : Triple.BOClass n' m T) :
    maxContactCase T hT hH hle bd = maxContactCase T hT' hH hle bd' := by
  unfold maxContactCase
  split_ifs with h
  · exact step2Seq_congr bd bd' hbd (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
      (le_of_eq (maxOrd_tuned h hT.1)) (one_le_tuningParam m) hH
      (retune_keeps_maxContact h hT.1 hle) (hasDimLE_tuned hT'.2.1 m hT.1)
  · rfl

end Step22

section Global

variable (m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} n m j) (bd' : ∀ m j : ℕ, BDData.{u} n' m j)
  (hbd : ∀ (m j : ℕ) (T₀ : Triple k) (h₁ : Triple.BDClass n m j T₀)
    (h₂ : Triple.BDClass n' m j T₀),
    ((bd m j).functor k).seq T₀ h₁ = ((bd' m j).functor k).seq T₀ h₂)

include hbd in
/-- Congruence of the functor of [Kol07, Theorem 103] in the dimension bound (Step 3 of its proof
and the uniqueness of [Kol07, Theorem 105]): `BO_{n,m}` and `BO_{n',m}` (`n' ≤ n`), from pointwise
agreeing Lemma 102 data, take the same value at a triple of the smaller class. The stage-`n` functor
restricted to `BOClass n' m` agrees with the stage-`n'` LOCAL functor on the local triples
(`functor_seq_localClass` at stage `n` through `boClass_mono`, `localFunctor_seq`,
`maxContactCase_congr`) and commutes with surjective open-immersion coproducts
(`functor_commutesWithSmoothSurjections`, restricted), as does the stage-`n'` functor;
`globalization_unique` at the stage-`n'` classes identifies the two functors. `globalize` is never
unfolded. -/
theorem functor_congr (hle : n' ≤ n) (T : Triple k) (hT : Triple.BOClass n m T)
    (hT' : Triple.BOClass n' m T) :
    (functor (k := k) n m bd).seq T hT = (functor (k := k) n' m bd').seq T hT' := by
  have key : (functor (k := k) n m bd).restrict (Triple.BOClass n' m)
      (fun _ h => Triple.boClass_mono hle h) = functor (k := k) n' m bd' := by
    have h₁ : ∀ (T₀ : Triple k) (hL : localClass n' m T₀) (hG : Triple.BOClass n' m T₀),
        ((functor (k := k) n m bd).restrict (Triple.BOClass n' m)
          (fun _ h => Triple.boClass_mono hle h)).seq T₀ hG =
          (localFunctor n' m bd').seq T₀ hL := by
      intro T₀ hL hG
      obtain ⟨-, H, hH, hmc⟩ := hL
      rw [OrderSeqAssignment.restrict_seq, functor_seq_localClass n m bd T₀ _ hH hmc,
        localFunctor_seq n' m bd' T₀ ⟨hG, H, hH, hmc⟩ hH hmc]
      exact maxContactCase_congr bd bd' hbd T₀ hH hmc _ hG
    have h₂ : ∀ (T₀ : Triple k) (hL : localClass n' m T₀) (hG : Triple.BOClass n' m T₀),
        (functor (k := k) n' m bd').seq T₀ hG = (localFunctor n' m bd').seq T₀ hL := by
      intro T₀ hL hG
      obtain ⟨-, H, hH, hmc⟩ := hL
      rw [functor_seq_localClass n' m bd' T₀ hG hH hmc,
        localFunctor_seq n' m bd' T₀ ⟨hG, H, hH, hmc⟩ hH hmc]
    have c₁ : ((functor (k := k) n m bd).restrict (Triple.BOClass n' m)
        (fun _ h => Triple.boClass_mono hle h)).CommutesWithSurjectionsIn
          openImmersionCoprods :=
      OrderSeqAssignment.restrict_commutesWithSurjectionsIn _ _ _
        ((functor_commutesWithSmoothSurjections n m bd).commutesWithSurjectionsIn
          isGlobalizationClass_openImmersionCoprods)
    have c₂ : (functor (k := k) n' m bd').CommutesWithSurjectionsIn openImmersionCoprods :=
      (functor_commutesWithSmoothSurjections n' m bd').commutesWithSurjectionsIn
        isGlobalizationClass_openImmersionCoprods
    exact OrderSeqAssignment.globalization_unique (k := k) (m := m) (GT := Triple.BOClass n' m)
      (LT := localClass n' m) (globalizationData_localClass n' m) (fun _ h => h.1)
      (localFunctor n' m bd') h₁ h₂ c₁ c₂
  exact congrArg (fun B : OrderSeqAssignment k m (Triple.BOClass n' m) => B.seq T hT') key

end Global

/-- Congruence of [Kol07, Theorem 103] as data (`BO.data`) in the dimension bound: at stages `n` and
`n' ≤ n`, from inductive inputs that agree on the marked triples of dimension `≤ n' − 1`, it takes
the same value at a triple of both classes — `functor_congr` at `bdData`, whose congruence is
`bdData_congr`. -/
theorem data_congr {n n' m : ℕ} (hle : n' ≤ n)
    (Dom Dom' : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (B' : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom' k))
    (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hDom' : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n' - 1) → T'.m = tuningParam m → Dom' k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hB' : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom' k T'),
      ((B' k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hsm' : ∀ (k : Type u) [Field k] [CharZero k], (B' k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hbc' : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B' k).CommutesWithBaseChange (B' L) σ)
    (hBind : ∀ (k : Type u) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers)
    (hBind' : ∀ (k : Type u) [Field k] [CharZero k], (B' k).IndifferentToEmptyMembers)
    (hagree : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (h₁ : Dom k T')
      (h₂ : Dom' k T'), T'.toTriple.HasDimLE (n' - 1) → (B k).seq T' h₁ = (B' k).seq T' h₂)
    (k : Type u) [Field k] [CharZero k] (T : Triple k) (hT : T.BOClass n m) (hT' : T.BOClass n' m) :
    ((data n m Dom B hDom hB hsm hbc hBind).functor k).seq T hT =
      ((data n' m Dom' B' hDom' hB' hsm' hbc' hBind').functor k).seq T hT' :=
  functor_congr m (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc)
    (fun m j => Hironaka.BD.bdData n' m j Dom' B' (hDom' m) hB' hsm' hbc')
    (fun m _ T₀ h₁ h₂ => Hironaka.BD.bdData_congr Dom Dom' B B' (hDom m) (hDom' m) hB hB' hsm hsm'
      hbc hbc' hagree k T₀ h₁ h₂) hle T hT hT'

end Hironaka.BO
