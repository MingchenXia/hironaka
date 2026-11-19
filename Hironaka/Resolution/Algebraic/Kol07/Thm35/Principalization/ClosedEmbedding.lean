/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
public import Hironaka.Scheme.Snc.EmptyFamily
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Basic
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingGeneral
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The principalization sequence commutes with closed embeddings when `E = ∅`

Clause (5) of [Kol07, Theorem 35], the functoriality for closed embeddings of [Kol07, 34.3]: for a
closed embedding `j : Y ↪ X` of smooth `k`-schemes with `𝒪_X/I_X = j_*(𝒪_Y/I_Y)` and `E = ∅`,
`BP(X, I_X, ∅) = j_* BP(Y, I_Y, ∅)`. With `E` empty the disjoining part of `BP` is empty
(`BP_of_isEmpty`: `BP T = BMO_1(X, I, 1, ∅)`), so the clause is exactly [Kol07, Claim 71.2] for
`BMO_1`, "the functoriality properties required in (35) follow … from (71.2)" [Kol07, 72]. Claim
71.2 is proved in `Hironaka/Resolution/Algebraic/Stage/ClosedEmbeddingGeneral.lean` for the functor
at a fixed dimension (`Hironaka.Stage.tower_bmo_one_eq_pushforward_closedEmbedding_aux`); it is read
here at the dimension of
`X` through `dimFreeBMO_seq_eq_tower` (`BMO_1` is the dimension-free functor, and the closed
subscheme `Y` has dimension `≤ dim X`, `bmoClass_of_closedEmbedding`). `BP_eq_of_isEmpty`
says that `BP` does not see how an empty boundary is indexed, through the indifference of `BMO_1`
to unit members; with it the clause holds for any empty boundary on `Y`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Hironaka.Stage

namespace Hironaka.Sequence

variable {k : Type u} [Field k] [CharZero k]

/-- Clause (5) of [Kol07, Theorem 35]: for a closed embedding `j : Y ↪ X` carrying
`𝒪_X/I_X = j_*(𝒪_Y/I_Y)` and `E = ∅`, `BP(X, I_X, ∅) = j_* BP(Y, I_Y, j^{-1} ∅)`. The disjoining
part is empty (`BP_of_isEmpty`) and the `BMO_1` part is [Kol07, Claim 71.2] at the dimension of
`X`. -/
theorem BP_pushforward_of_closedEmbedding (TX TY : Triple k) (j : TY.X.left ⟶ TX.X.left)
    [IsClosedImmersion j] (hj : TX.ClosedEmbedding TY j) (hE : IsEmpty TX.E.ι) :
    BP TX = (BP TY).pushforward j := by
  have hEY : IsEmpty TY.E.ι := by
    rw [hj.2.2]
    exact hE
  have hmj : MarkedTriple.ClosedEmbedding ⟨TX, 1⟩ ⟨TY, 1⟩ j := ⟨hj, rfl⟩
  have hTX : (⟨TX, 1⟩ : MarkedTriple k).BMOClass TX.dim 1 :=
    MarkedTriple.bmoClass_of_bmoClassFree ⟨le_rfl, rfl⟩
  rw [BP_of_isEmpty TX hE, BP_of_isEmpty TY hEY]
  change (dimFreeBMO stage0 1 k).seq ⟨TX, 1⟩ ⟨le_rfl, rfl⟩ =
    ((dimFreeBMO stage0 1 k).seq ⟨TY, 1⟩ ⟨le_rfl, rfl⟩).pushforward j
  rw [dimFreeBMO_seq_eq_tower stage0 1 TX.dim ⟨TX, 1⟩ ⟨le_rfl, rfl⟩ hTX]
  refine (Hironaka.Stage.tower_bmo_one_eq_pushforward_closedEmbedding_aux stage0 TX.dim ⟨TX, 1⟩
    ⟨TY, 1⟩ j hmj hE
    hTX).trans ?_
  exact congrArg (fun S : BlowUpSequence TY.X.left => S.pushforward j)
    (dimFreeBMO_seq_eq_tower stage0 1 TX.dim ⟨TY, 1⟩ ⟨le_rfl, rfl⟩
      (bmoClass_of_closedEmbedding hmj hTX)).symm

/-- `BP` does not see how an empty boundary is indexed: two triples on the same `(X, I)` whose
boundaries both have empty index type have the same principalization sequence (the indifference of
`BMO_1` to unit members, at the dimension of `X`). -/
theorem BP_eq_of_isEmpty (T : Triple k) (E' : DivisorFamily T.X.left) (hE' : E'.IsSnc)
    (hE : IsEmpty T.E.ι) [IsEmpty E'.ι] :
    BP T = BP { T with E := E', isSnc := hE' } := by
  have hT : (⟨T, 1⟩ : MarkedTriple k).BMOClass T.dim 1 :=
    MarkedTriple.bmoClass_of_bmoClassFree ⟨le_rfl, rfl⟩
  rw [BP_of_isEmpty T hE, BP_of_isEmpty _ ‹IsEmpty E'.ι›]
  change (dimFreeBMO stage0 1 k).seq ⟨T, 1⟩ ⟨le_rfl, rfl⟩ =
    (dimFreeBMO stage0 1 k).seq ⟨{ T with E := E', isSnc := hE' }, 1⟩ ⟨le_rfl, rfl⟩
  have hT' : (⟨{ T with E := E', isSnc := hE' }, 1⟩ : MarkedTriple k).BMOClass T.dim 1 := hT
  rw [dimFreeBMO_seq_eq_tower stage0 1 T.dim ⟨T, 1⟩ ⟨le_rfl, rfl⟩ hT,
    dimFreeBMO_seq_eq_tower stage0 1 T.dim ⟨{ T with E := E', isSnc := hE' }, 1⟩ ⟨le_rfl, rfl⟩ hT']
  exact ((tower stage0 T.dim).bmo 1).indifferentToEmptyMembers k ⟨T, 1⟩ E' hE'
    OrderEmbedding.ofIsEmpty (fun i => isEmptyElim i) (fun b _ => hE.elim b) hT hT'

end Hironaka.Sequence
