/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
public import Hironaka.Scheme.BlowUpSequence.Functor
public import Hironaka.Scheme.Snc.AppendEmpty
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The data of marked order reduction: reading the fields

The fields of `BMOData n m`, read
the way Kollár prints [Kol07, Theorem 107] and the way the later constructions use them.

* `bmoClass_iff`: the domain unfolds (`Iff.rfl`, the class is an `abbrev`).
* `BMOData.ord_markedTransformSeq_lt`: clause (1) pointwise, `ord_x I_r ≤ max-ord I_r < m`.
* `BMOData.markedCosupp_eq_empty`: clause (1) as the proof of Theorem 107 reaches it,
  `cosupp(I_r, m) = ∅` ([Kol07, 111]): no point has `ord_x I_r ≥ m`.
* `BMOData.maxOrd_endTriple_lt`: clause (1) in the form the boundary-clearing functor of
  [Kol07, Lemma 102] and the order-reduction data `BO.data` take: the end triple's ideal is the
  last marked transform by `rfl`, and the class fixes the mark, `T.m = m`.
* `BMOData.seq_append_top`: the indifference field along the order embedding `i ↦ toLex (inl i)`
  of `E.ι` into `(E.append ⊤).ι = E.ι ⊕ₗ PUnit` ([Kol07, 32]; the form needed for clause (3) of
  Lemma 102): the members are matched along the embedding and the one index outside its range,
  `inr ()`, carries the unit ideal; the triple with the appended member is `T` with
  `E := E.append ⊤` (normal crossings by `isSnc_append_top`), and the field's other triple is `T`
  itself by structure eta.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka

variable {k : Type u} [Field k]

/-- The domain of `BMO_{n,m}` unfolds: `1 ≤ m`, `dim X ≤ n` and `T.m = m`. -/
theorem MarkedTriple.bmoClass_iff (n m : ℕ) (T : MarkedTriple k) :
    MarkedTriple.BMOClass n m T ↔ 1 ≤ m ∧ T.toTriple.HasDimLE n ∧ T.m = m :=
  Iff.rfl

namespace BMOData

open Scheme

variable [CharZero k] {n m : ℕ} (B : BMOData.{u} n m) (T : MarkedTriple k)
  (hT : MarkedTriple.BMOClass n m T)

/-- Clause (1) of [Kol07, Theorem 107] pointwise, through `ord_x I_r ≤ max-ord I_r`. -/
theorem ord_markedTransformSeq_lt (x : ((B.functor k).seq T hT).stage (Fin.last _)) :
    (((B.functor k).seq T hT).markedTransformSeq T.I T.m (Fin.last _)).ord x < (m : ℕ∞) :=
  lt_of_le_of_lt (Scheme.IdealSheafData.le_maxOrd _ x) (B.maxOrd_lt k T hT)

/-- Clause (1) of [Kol07, Theorem 107] as the emptiness of the cosupport, `cosupp(I_r, m) = ∅`
(the form reached at the end of [Kol07, 111]). -/
theorem markedCosupp_eq_empty :
    {x : ((B.functor k).seq T hT).stage (Fin.last _) |
      (m : ℕ∞) ≤ (((B.functor k).seq T hT).markedTransformSeq T.I T.m (Fin.last _)).ord x} =
      ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx =>
    (not_lt.mpr hx) (B.ord_markedTransformSeq_lt T hT x)

/-- Clause (1) of [Kol07, Theorem 107] for the end triple: its ideal has `max-ord < T.m`. The end
triple's ideal is the last marked transform by `rfl` (`induced_I`), and the class fixes
`T.m = m`. -/
theorem maxOrd_endTriple_lt : ((B.functor k).endTriple T hT).I.maxOrd < (T.m : ℕ∞) :=
  lt_of_lt_of_eq (B.maxOrd_lt k T hT) (by rw [hT.2.2])

/-- The indifference field in the appended-member form ([Kol07, 32]; the form needed for clause (3)
of [Kol07, Lemma 102]): the value on `T` with the unit ideal appended to its boundary is the value
on `T`. The embedding is `i ↦ toLex (inl i)`; the index `inr ()` outside its range carries `⊤`. -/
theorem seq_append_top
    (hT' : MarkedTriple.BMOClass n m
      { T with E := T.E.append ⊤, isSnc := DivisorFamily.isSnc_append_top T.E T.isSnc }) :
    (B.functor k).seq T hT =
      (B.functor k).seq
        { T with E := T.E.append ⊤, isSnc := DivisorFamily.isSnc_append_top T.E T.isSnc } hT' := by
  let e : T.E.ι ↪o (T.E.append ⊤).ι :=
    OrderEmbedding.ofStrictMono (fun i => toLex (Sum.inl i))
      (fun a b h => Sum.Lex.inl_lt_inl_iff.mpr h)
  have h1 : ∀ i, (T.E.append ⊤).component (e i) = T.E.component i := fun _ => rfl
  have h2 : ∀ b, b ∉ Set.range e → (T.E.append ⊤).component b = ⊤ := by
    intro b hb
    rcases b with i | u
    · exact absurd ⟨i, rfl⟩ hb
    · rfl
  exact (B.indifferentToEmptyMembers k
    { T with E := T.E.append ⊤, isSnc := DivisorFamily.isSnc_append_top T.E T.isSnc }
    T.E T.isSnc e h1 h2 hT' hT).symm

end BMOData

end Hironaka
