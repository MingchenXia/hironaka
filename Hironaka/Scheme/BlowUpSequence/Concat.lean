/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# Concatenation of blow-up sequences

Blow-up sequences [Kol07, Definition 29] compose: a sequence `S` on `X` of length `r` ending at
`X_r`, followed by a sequence `T` on `X_r` of length `s`, is a sequence on `X` of length `r + s`
with composite `Π_T ≫ Π_S` (Kollár's `Π_{ij}` bookkeeping; the disjoining sequence "composed on
the right" with the marked order reduction functor in [Kol07, 72] is the same operation). On the
inductive type `AlgebraicGeometry.Scheme.BlowUpSequence` (`nil`, and `cons X D rest` with `rest`
living on `D.blowUp`) the concatenation is the structural recursion below: the tail of `cons X D
rest` is a sequence on `blowUp X D` whose last stage is definitionally `(cons X D rest).last`, so
the second argument needs no transport.

Concatenation is used to refine a smooth blow-up sequence to one with irreducible centers (each
center `Z_i` is replaced by the sequence blowing up its components one at a time,
`Hironaka/Resolution/Algebraic/Kol07/Componentwise.lean`, and the remainder of the sequence, carried
across the canonical isomorphism of the end results, is concatenated on the right), and to assemble
the rounds of the order reduction and resolution algorithms into one sequence.

## Main declarations

* `AlgebraicGeometry.Scheme.BlowUpSequence.concat S T`: the concatenation `S ++ T` for
  `T : BlowUpSequence S.last`.
* `concat_nil`, `concat_cons` (the recursion), `length_concat`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.BlowUpSequence

variable {X : Scheme.{u}}

/-- The concatenation of a blow-up sequence `S` on `X` with a blow-up sequence `T` on its last
stage `S.last`: the sequence performing the blow-ups of `S` and then those of `T`
[Kol07, Definition 29]. -/
noncomputable def concat :
    {X : Scheme.{u}} → (S : BlowUpSequence X) → BlowUpSequence S.last → BlowUpSequence X
  | _, nil X, T => T
  | _, cons X D rest, T => cons X D (rest.concat T)

@[simp]
theorem concat_nil (T : BlowUpSequence (nil X).last) : (nil X).concat T = T := rfl

@[simp]
theorem concat_cons (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (T : BlowUpSequence (cons X D rest).last) :
    (cons X D rest).concat T = cons X D (rest.concat T) := rfl

/-- The length of a concatenation is the sum of the lengths (Kollár's `r + s`). -/
theorem length_concat (S : BlowUpSequence X) (T : BlowUpSequence S.last) :
    (S.concat T).length = S.length + T.length := by
  induction S with
  | nil X => exact (Nat.zero_add _).symm
  | cons X D rest ih =>
    change (rest.concat T).length + 1 = rest.length + 1 + T.length
    rw [ih T]
    exact Nat.add_right_comm _ _ _

end AlgebraicGeometry.Scheme.BlowUpSequence
