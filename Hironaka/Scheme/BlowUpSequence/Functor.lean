/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Blow-up sequence functors on triples and marked triples

A blow-up sequence functor [Kol07, Definition 31] is, after the last paragraph of
[Kol07, Definition 66], an assignment `(X, I, E) ↦ B(X, I, E)` of a smooth blow-up sequence of
order `m` starting with the input, on a class of triples. In this library it is the structure
`Hironaka.OrderSeqAssignment k m Dom` of
`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean` (a
field `seq` on the class `Dom`, the order proof `isOrderSeq`, and the empty blow-up convention of
[Kol07, 32] as the field `noEmptyCenters`), with the marked version `OrderGeSeqFunctor k Dom`.
This module proves the elementary facts about them and defines the induced triples.

* Extensionality (`ext`): the last two fields are proofs, so a functor is its `seq`; after
  destructing both structures the equation between the `seq` fields is substituted and the
  remaining proof fields agree by proof irrelevance.
* The induced triples (`induced`, `endTriple`): Kollár's "we consider the sheaves `I_i` and the
  divisors `E_i` as part of the functor" is realised by applying `Triple.induced`
  (`Hironaka/Scheme/BlowUpSequence/Triple.lean`) to the functor's own sequence and its own order
  proof; the end triple `Π_*^{-1}(X, I, E) = (X_r, I_r, E_r)` is its value at the last index, and
  its underlying scheme is the first component of the resolution functor's value `endResult`
  (`endTriple_X`, by `rfl`: both are `stage (Fin.last _)`).
* The resolution functor (`endResult_fst`, `endResult_snd`, `isProper_endResult`): the value
  `(Π : X_r → X)` is `⟨last, composite⟩` by definition; `Π` is the stage map at the last index,
  proper as a composite of blow-ups of a locally Noetherian scheme (`isProper_stageMap`).
* The empty blow-up convention (`eraseEmpty_seq`, `center_ne_top`, `ofEraseEmpty`): the field
  `noEmptyCenters` says no center is `⊤`, so `eraseEmpty_eq_self_iff` gives
  `del(B(X, I, E)) = B(X, I, E)`; the packaging `ofEraseEmpty` deletes the empty blow-ups of an
  assignment and takes `noEmptyCenters_eraseEmpty` for the convention, its order field being the
  hypothesis that the deleted sequences are of order `m` (`IsOrderSeq.eraseEmpty` of
  `Hironaka/Scheme/BlowUpSequence/PullbackEraseEmpty.lean` supplies it from the undeleted ones).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.BlowUpSequence

namespace Hironaka.OrderSeqAssignment

open Scheme.IdealSheafData Scheme

variable {k : Type u} [Field k]

variable {m : ℕ} {Dom : Triple k → Prop}

/-- A blow-up sequence functor is its assignment of sequences [Kol07, Definition 31]. -/
theorem ext {B B' : OrderSeqAssignment k m Dom}
    (h : ∀ T (hT : Dom T), B.seq T hT = B'.seq T hT) : B = B' := by
  have hs : B.seq = B'.seq := funext fun T => funext fun hT => h T hT
  cases B; cases B'; cases hs; rfl

/-- The triple `(X_i, I_i, E_i)` induced at stage `i` of `B(X, I, E)`
[Kol07, Definition 66, last paragraph]. -/
noncomputable def induced [CharZero k] (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) : Triple k :=
  T.induced (B.seq T h) (B.isOrderSeq T h) i

/-- `Π_*^{-1}(X, I, E) = (X_r, I_r, E_r)`, the triple induced at the end of `B(X, I, E)`
[Kol07, Definition 66, last paragraph]. -/
noncomputable def endTriple [CharZero k] (B : OrderSeqAssignment k m Dom) (T : Triple k)
    (h : Dom T) :
    Triple k :=
  B.induced T h (Fin.last _)

theorem induced_X [CharZero k] (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) : (B.induced T h i).X.left = (B.seq T h).stage i :=
  rfl

theorem induced_I [CharZero k] (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) :
    (B.induced T h i).I = (B.seq T h).weakTransformSeq T.I i :=
  rfl

theorem induced_E [CharZero k] (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) :
    (B.induced T h i).E = (B.seq T h).totalTransformSeq T.E i :=
  rfl

/-- The underlying scheme of `Π_*^{-1}(X, I, E)` is the scheme of the end result `R(X, I, E)`. -/
theorem endTriple_X [CharZero k] (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T) :
    (B.endTriple T h).X.left = (B.endResult T h).1 :=
  rfl

/-- The end result of `B(X, I, E)` is the last stage `X_r` [Kol07, Definition 31]. -/
theorem endResult_fst (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T) :
    (B.endResult T h).1 = (B.seq T h).last :=
  rfl

/-- The morphism of the end result is the composite `Π : X_r → X` [Kol07, Definition 31]. -/
theorem endResult_snd (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T) :
    (B.endResult T h).2 = (B.seq T h).composite :=
  rfl

/-- The end result `Π : X_r → X` of [Kol07, Definition 31] is proper: it is the stage map at the
last index, a composite of blow-ups (`isProper_stageMap`). -/
theorem isProper_endResult (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T) :
    IsProper (B.endResult T h).2 := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact isProper_stageMap (B.seq T h) (Fin.last _)

/-- Deleting the empty blow-ups of a value of the functor changes nothing [Kol07, 32]. -/
theorem eraseEmpty_seq (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T) :
    (B.seq T h).eraseEmpty = B.seq T h :=
  (eraseEmpty_eq_self_iff _).2 (B.noEmptyCenters T h)

/-- No center of a value of the functor is empty [Kol07, 32]. -/
theorem center_ne_top (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T)
    (i : Fin (B.seq T h).length) : (B.seq T h).center i ≠ ⊤ :=
  B.noEmptyCenters T h i

/-- The functor packaging an assignment of sequences after deleting their empty blow-ups
[Kol07, 32], given that the deleted sequences are of order `m`. -/
noncomputable def ofEraseEmpty (seq : ∀ T : Triple k, Dom T → BlowUpSequence T.X.left)
    (h : ∀ T (hT : Dom T),
      (seq T hT).eraseEmpty.IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m) :
    OrderSeqAssignment k m Dom where
  seq T hT := (seq T hT).eraseEmpty
  isOrderSeq := h
  noEmptyCenters T hT := noEmptyCenters_eraseEmpty (seq T hT)

theorem ofEraseEmpty_seq (seq : ∀ T : Triple k, Dom T → BlowUpSequence T.X.left)
    (h : ∀ T (hT : Dom T),
      (seq T hT).eraseEmpty.IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m)
    (T : Triple k) (hT : Dom T) : (ofEraseEmpty seq h).seq T hT = (seq T hT).eraseEmpty :=
  rfl

end Hironaka.OrderSeqAssignment

namespace Hironaka.OrderGeSeqAssignment

open Scheme.IdealSheafData Scheme

variable {k : Type u} [Field k]

variable {Dom : MarkedTriple k → Prop}

/-- A marked blow-up sequence functor is its assignment of sequences
[Kol07, Definition 66, last paragraph]. -/
theorem ext {B B' : OrderGeSeqAssignment k Dom}
    (h : ∀ T (hT : Dom T), B.seq T hT = B'.seq T hT) : B = B' := by
  have hs : B.seq = B'.seq := funext fun T => funext fun hT => h T hT
  cases B; cases B'; cases hs; rfl

/-- The marked triple `(X_i, I_i, m, E_i)` induced at stage `i` of `B(X, I, m, E)`
[Kol07, Definition 66, last paragraph]. -/
noncomputable def induced [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k)
    (h : Dom T) (i : Fin ((B.seq T h).length + 1)) : MarkedTriple k :=
  T.induced (B.seq T h) (B.isOrderGeSeq T h) i

/-- `Π_*^{-1}(X, I, m, E) = (X_r, I_r, m, E_r)`, the marked triple induced at the end of
`B(X, I, m, E)` [Kol07, Definition 66, last paragraph]. -/
noncomputable def endTriple [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k)
    (h : Dom T) : MarkedTriple k :=
  B.induced T h (Fin.last _)

theorem induced_X [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) : (B.induced T h i).X.left = (B.seq T h).stage i :=
  rfl

theorem induced_I [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) :
    (B.induced T h i).I = (B.seq T h).markedTransformSeq T.I T.m i :=
  rfl

theorem induced_m [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) : (B.induced T h i).m = T.m :=
  rfl

theorem induced_E [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T)
    (i : Fin ((B.seq T h).length + 1)) :
    (B.induced T h i).E = (B.seq T h).totalTransformSeq T.E i :=
  rfl

/-- The underlying scheme of `Π_*^{-1}(X, I, m, E)` is the scheme of the end result. -/
theorem endTriple_X [CharZero k] (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T) :
    (B.endTriple T h).X.left = (B.endResult T h).1 :=
  rfl

/-- The end result of `B(X, I, m, E)` is the last stage `X_r` [Kol07, Definition 31]. -/
theorem endResult_fst (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T) :
    (B.endResult T h).1 = (B.seq T h).last :=
  rfl

/-- The morphism of the end result of `B(X, I, m, E)` is the composite `Π : X_r → X`
[Kol07, Definition 31]. -/
theorem endResult_snd (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T) :
    (B.endResult T h).2 = (B.seq T h).composite :=
  rfl

/-- The end result of a marked blow-up sequence functor is proper. -/
theorem isProper_endResult (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T) :
    IsProper (B.endResult T h).2 := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact isProper_stageMap (B.seq T h) (Fin.last _)

/-- Deleting the empty blow-ups of a value of a marked functor changes nothing [Kol07, 32]. -/
theorem eraseEmpty_seq (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T) :
    (B.seq T h).eraseEmpty = B.seq T h :=
  (eraseEmpty_eq_self_iff _).2 (B.noEmptyCenters T h)

/-- No center of a value of a marked functor is empty [Kol07, 32]. -/
theorem center_ne_top (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T)
    (i : Fin (B.seq T h).length) : (B.seq T h).center i ≠ ⊤ :=
  B.noEmptyCenters T h i

/-- The marked functor packaging an assignment of sequences after deleting their empty blow-ups
[Kol07, 32]. -/
noncomputable def ofEraseEmpty (seq : ∀ T : MarkedTriple k, Dom T → BlowUpSequence T.X.left)
    (h : ∀ T (hT : Dom T),
      (seq T hT).eraseEmpty.IsOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.m T.E) :
    OrderGeSeqAssignment k Dom where
  seq T hT := (seq T hT).eraseEmpty
  isOrderGeSeq := h
  noEmptyCenters T hT := noEmptyCenters_eraseEmpty (seq T hT)

theorem ofEraseEmpty_seq (seq : ∀ T : MarkedTriple k, Dom T → BlowUpSequence T.X.left)
    (h : ∀ T (hT : Dom T),
      (seq T hT).eraseEmpty.IsOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.m T.E)
    (T : MarkedTriple k) (hT : Dom T) : (ofEraseEmpty seq h).seq T hT = (seq T hT).eraseEmpty :=
  rfl

end Hironaka.OrderGeSeqAssignment

