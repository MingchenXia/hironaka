/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Assembly
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalFamilyErasure
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.Monomial.Geometric.RealizeNil
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.IdealSheaf.Order.MaxOrdAnti
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (3) of marked order reduction: agreement with order reduction for ideals

Clause (3) of [Kol07, Theorem 107]: `BMO_{n,m}(X, I, m, ∅) = BO_{n,m}(X, I, ∅)` when
`m = max-ord I`. Kollár's proof, the last paragraph of [Kol07, 111]: for `E = ∅` one has
`N(I) = I`; if moreover `m = max-ord I`, Step 1 consists of the single round `BO_{n,m}(X, I, ∅)`,
each of whose blow-ups has order exactly `m`, so the birational transforms of `I` agree with those
of `(I, m)`; at the end of Step 1 the cosupport of `(I_1, m)` is empty and `M(I_1) = 𝒪_{X¹}`, so
Steps 2 and 3 do nothing. In the assembled functor
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Assembly.lean`):

* the round order of `(X, I, m, ∅)` is `m` (`N(I) = I`, `max-ord I = m`), so Step 1 unrolls to one
  round followed by the empty sequence (`step1_of_le`, `step1_of_lt`), the round being `BO_{n,m}`
  on `(X, N(I), ∅) = (X, I, ∅)` (`step1Round`);
* along that round, of order exactly `m`, the marked transform of `(I, m)` is the weak transform
  ([Kol07, Remark 67]; `IsOrderSeq.markedTransformSeq_eq_weakTransformSeq`), of `max-ord < m` at
  the end (clause (1) of [Kol07, Theorem 103]); so the induced marked triple has
  `cosupp(I_1, m) = ∅`, separation order `0` (Step 2 is empty, `step2_of_eq_zero`) and
  `max-ord M(I_1) ≤ max-ord I_1 < m` (Step 3 is empty, `step3Seq_eq_nil_of_maxOrd_lt`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Monomial Hironaka.Monomial.PieceFamily Hironaka.Sequence

namespace Hironaka.BMO

section Step3Nil

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k) {n m : ℕ}

/-- Below the mark, `max-ord M(I) < m`, Step 3 is the empty sequence (the last paragraph of
[Kol07, 111]: "`M(…) = 𝒪_{X¹}` … Steps 2 and 3 do nothing"): every face of the input state has
exponent sum `< m` (`star_toState_of_maxOrd_lt` through `monomial_exponentAt_step3Family`), so the
combinatorial run is empty and its realization is `nil` (`realize_eq_nil`). -/
theorem step3Seq_eq_nil_of_maxOrd_lt (hT : T.BMOClass n m)
    (h : (monomialPart T.I T.E).maxOrd < (m : ℕ∞)) : step3Seq T hT =
      BlowUpSequence.nil T.X.left := by
  have := T.smooth
  refine realize_eq_nil (T.X.left ↘ Spec (.of k)) (step3Family T) (step3Family_isValid T hT) ?_
  refine star_toState_of_maxOrd_lt (T.X.left ↘ Spec (.of k)) (step3Family T) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) ?_
  rwa [monomial_exponentAt_step3Family]

end Step3Nil

section Concat

variable {X : Scheme.{u}}

/-- A concatenation of two empty sequences is empty. -/
theorem concat_eq_nil_of_eq_nil {S : BlowUpSequence X} {R : BlowUpSequence S.last}
    (hS : S = BlowUpSequence.nil X) (hR : R = BlowUpSequence.nil _) :
    S.concat R = BlowUpSequence.nil X := by
  subst hS
  exact hR

end Concat

section Clause3

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}

/-- The value of `BO_{n,d}` on a triple depends only on the mark and the triple, not on the proof
of membership in the class (proof irrelevance, through the equalities of marks and triples). -/
theorem functor_seq_heq {d d' : ℕ} (hdd : d = d') {T T' : Triple k} (hTT : T = T')
    (hT : Triple.BOClass n d T) (hT' : Triple.BOClass n d' T') :
    HEq (((bo d).functor k).seq T hT) (((bo d').functor k).seq T' hT') := by
  subst hdd
  subst hTT
  rfl

omit [CharZero k] in
/-- For the empty boundary the triple `(X, N(I), E)` of the round is the triple itself (the last
paragraph of [Kol07, 111]: "if `E = ∅` then `N(I) = I`"). -/
theorem nonmonomialTriple_eq_of_isEmpty (T : Triple k) (hE : IsEmpty T.E.ι) :
    nonmonomialTriple (⟨T, m⟩ : MarkedTriple k) = T := by
  have hN : nonmonomialPart T.I T.E = T.I := nonmonomialPart_of_isEmpty T hE
  cases T
  simp only [nonmonomialTriple] at hN ⊢
  simp only [hN]

/-- **For `E = ∅` and `m = max-ord I`, `BMO_{n,m}(X, I, m, ∅) = BO_{n,m}(X, I, ∅)`** as blow-up
sequences (clause (3) of [Kol07, Theorem 107]): Step 1 is the single round
`BO_{n,m}(X, N(I), ∅) = BO_{n,m}(X, I, ∅)` (the round order is `m`, and after it the round order is
`< m`); along it the marked and the birational transforms agree ([Kol07, Remark 67]), so
`cosupp((I_1, m)) = ∅`, whence Step 2 is empty (separation order `0`) and Step 3 is empty
(`max-ord M(I_1) ≤ max-ord I_1 < m`). -/
theorem eq_BO_of_maxOrd (T : Triple k) (hT : T.BOClass n m) (hE : IsEmpty T.E.ι)
    (hmax : T.I.maxOrd = (m : ℕ∞)) :
    (functor bo m).seq ⟨T, m⟩ (bmoClass_of_boClass T hT) = ((bo m).functor k).seq T hT := by
  have hTc : MarkedTriple.BMOClass n m (⟨T, m⟩ : MarkedTriple k) := bmoClass_of_boClass T hT
  have hN : nonmonomialPart T.I T.E = T.I := nonmonomialPart_of_isEmpty T hE
  -- the round order is `m`
  have hr : roundOrder (⟨T, m⟩ : MarkedTriple k) = m := by
    have h' : (roundOrder (⟨T, m⟩ : MarkedTriple k) : ℕ∞) = (m : ℕ∞) := by
      rw [coe_roundOrder]
      change (nonmonomialPart T.I T.E).maxOrd = (m : ℕ∞)
      rw [hN, hmax]
    exact_mod_cast h'
  have hd : m ≤ roundOrder (⟨T, m⟩ : MarkedTriple k) := hr.ge
  -- Step 1 is the single round
  have hstep1 : (step1 bo ⟨T, m⟩ hTc).1 = step1Round bo ⟨T, m⟩ hTc hd := by
    rw [step1_of_le bo _ hTc hd]
    exact concat_eq_of_eq_nil _
      (step1_of_lt bo _ _ (lt_of_lt_of_eq (roundOrder_roundTriple_lt bo _ hTc hd) hr))
  -- along the round the marked transform is the birational transform (Remark 67), of maximal order
  obtain ⟨n', -, hn'⟩ := hT.2.1
  have hsm : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hmax1 : ((step1 bo ⟨T, m⟩ hTc).1.markedTransformSeq T.I m (Fin.last _)).maxOrd <
      (m : ℕ∞) := by
    rw [hstep1]
    have hseq := step1Round_isOrderSeq bo ⟨T, m⟩ hTc hd
    rw [hN, hr] at hseq
    rw [IsOrderSeq.markedTransformSeq_eq_weakTransformSeq (T.X.left ↘ Spec (.of k)) n' hseq]
    have hlt := maxOrd_weakTransformSeq_step1Round_lt bo ⟨T, m⟩ hTc hd
    rw [hN, hr] at hlt
    exact hlt
  -- Step 2 is empty: the separation order of the induced triple is `0`
  have hsep : sepOrder (afterStep1 bo ⟨T, m⟩ hTc) = 0 := by
    rw [sepOrder_eq_zero_iff, Set.disjoint_left]
    intro x hx _
    exact absurd hx (not_le.2 (lt_of_le_of_lt (IdealSheafData.le_maxOrd (I := _) x) hmax1))
  have h2 : (step2 bo (afterStep1 bo ⟨T, m⟩ hTc) (bmoClass_afterStep1 bo ⟨T, m⟩ hTc)).1 =
      BlowUpSequence.nil _ :=
    step2_of_eq_zero bo _ _ hsep
  -- Step 3 is empty: `max-ord M(I_1) ≤ max-ord I_1 < m`
  have hM : (monomialPart (afterStep2 bo ⟨T, m⟩ hTc).I (afterStep2 bo ⟨T, m⟩ hTc).E).maxOrd <
      (m : ℕ∞) := by
    change (monomialPart
      (BlowUpSequence.markedTransformSeq
        (step2 bo (afterStep1 bo ⟨T, m⟩ hTc) (bmoClass_afterStep1 bo ⟨T, m⟩ hTc)).1
        (afterStep1 bo ⟨T, m⟩ hTc).I (afterStep1 bo ⟨T, m⟩ hTc).m (Fin.last _))
      (BlowUpSequence.totalTransformSeq
        (step2 bo (afterStep1 bo ⟨T, m⟩ hTc) (bmoClass_afterStep1 bo ⟨T, m⟩ hTc)).1
        (afterStep1 bo ⟨T, m⟩ hTc).E (Fin.last _))).maxOrd < (m : ℕ∞)
    rw [h2]
    change (monomialPart (afterStep1 bo ⟨T, m⟩ hTc).I (afterStep1 bo ⟨T, m⟩ hTc).E).maxOrd <
      (m : ℕ∞)
    have hle : (afterStep1 bo ⟨T, m⟩ hTc).I ≤
        monomialPart (afterStep1 bo ⟨T, m⟩ hTc).I (afterStep1 bo ⟨T, m⟩ hTc).E :=
      calc (afterStep1 bo ⟨T, m⟩ hTc).I
          = monomialPart (afterStep1 bo ⟨T, m⟩ hTc).I (afterStep1 bo ⟨T, m⟩ hTc).E *
            nonmonomialPart (afterStep1 bo ⟨T, m⟩ hTc).I (afterStep1 bo ⟨T, m⟩ hTc).E :=
            (monomialPart_mul_nonmonomialPart (afterStep1 bo ⟨T, m⟩ hTc).toTriple).symm
        _ ≤ monomialPart (afterStep1 bo ⟨T, m⟩ hTc).I (afterStep1 bo ⟨T, m⟩ hTc).E :=
            IdealSheafData.mul_le_self_left _ _
    exact lt_of_le_of_lt (IdealSheafData.maxOrd_anti hle) hmax1
  have h3 : step3Seq (afterStep2 bo ⟨T, m⟩ hTc) (bmoClass_afterStep2 bo ⟨T, m⟩ hTc) =
      BlowUpSequence.nil _ :=
    step3Seq_eq_nil_of_maxOrd_lt _ _ hM
  -- assemble
  change bmoSeq bo ⟨T, m⟩ hTc = _
  unfold bmoSeq
  refine (concat_eq_of_eq_nil _ (concat_eq_nil_of_eq_nil h2 h3)).trans ?_
  rw [hstep1, step1Round_eq]
  exact eq_of_heq (functor_seq_heq bo hr (nonmonomialTriple_eq_of_isEmpty T hE) _ _)

end Clause3

end Hironaka.BMO
