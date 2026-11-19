/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Concatenation of blow-up sequences: the marked order condition and the end data

The marked order condition of [Kol07, Definition 66] (a smooth blow-up sequence of order `≥ m`
starting with `(X, I, m, E)`, `IsOrderGeSeq`) along a concatenation: a sequence of order `≥ m` for
`(X, I, m, E)` followed by one of order `≥ m` for the induced marked triple
`(X_r, Π^{-1}_*(I, m), m, Π^{-1}_{tot} E)` is a sequence of order `≥ m` for `(X, I, m, E)`. This is
the marked analogue of `isOrderSeq_concat` (`Hironaka/Scheme/BlowUpSequence/ConcatApi.lean`). In the
proof of Theorem 107 [Kol07, 111, Step 1] the order reduction of the nonmonomial part is a
concatenation of rounds, each of order `≥ m` for the marked ideal, and the second step concatenates
likewise.

* `isOrderGeSeq_concat`: the conditions (1′)–(4′) of Definition 66 concatenate.
* `markedEnd_concat_iff`: a property of the induced marked ideal and boundary at the end of a
  concatenation is the same property at the end of the second sequence for the first sequence's
  induced data, `Π^{-1}_{S ++ T *}(I, m) = Π^{-1}_{T *}(Π^{-1}_{S *}(I, m), m)` and
  `(S ++ T)^{-1}_{tot} E = T^{-1}_{tot}(S^{-1}_{tot} E)`, stated without a transport of the end
  results (the two ends are definitionally equal along the recursion on `S`), so that no
  `eqToHom` appears, as in `disjoint_cosupp_concat_iff` of
  `Hironaka/Scheme/BlowUpSequence/ConcatTransforms.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` followed by one of order `≥ m` for
the induced marked data at its end is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)`
[Kol07, Definition 66, conditions (1′)–(4′)]; the marked analogue of `isOrderSeq_concat`. -/
theorem isOrderGeSeq_concat {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E)
    (hT : T.IsOrderGeSeq (S.composite ≫ f) (S.markedTransformSeq I m (Fin.last _)) m
      (S.totalTransformSeq E (Fin.last _))) :
    (S.concat T).IsOrderGeSeq f I m E := by
  induction S with
  | nil X =>
    have h : (nil X).composite ≫ f = f := Category.id_comp f
    rw [h] at hT
    exact hT
  | cons X D rest ih =>
    obtain ⟨hhead, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 hS
    refine (isOrderGeSeq_cons_iff f I E m D (rest.concat T)).2 ⟨hhead, ?_⟩
    have h : (cons X D rest).composite ≫ f = rest.composite ≫ D.blowUpπ ≫ f :=
      Category.assoc _ _ _
    rw [h] at hT
    exact ih (D.blowUpπ ≫ f) T ht hT

/-- A property of the induced marked ideal and boundary at the end of `S ++ T` is the same
property at the end of `T` for the data induced by `S` [Kol07, Definition 66, condition (1′)],
stated without a transport of the end results, by recursion on `S` (`nil`: the two sides
coincide; `cons`: the recursive call on the tail with the one-step transforms). -/
theorem markedEnd_concat_iff
    (P : ∀ {Y : Scheme.{u}}, Y.IdealSheafData → DivisorFamily Y → Prop) (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X) :
    P ((S.concat T).markedTransformSeq I m (Fin.last _))
        ((S.concat T).totalTransformSeq E (Fin.last _)) ↔
      P (T.markedTransformSeq (S.markedTransformSeq I m (Fin.last _)) m (Fin.last _))
        (T.totalTransformSeq (S.totalTransformSeq E (Fin.last _)) (Fin.last _)) := by
  induction S with
  | nil X => exact Iff.rfl
  | cons X D rest ih => exact ih T (I.markedTransform D m) (E.totalTransform D)

end AlgebraicGeometry
