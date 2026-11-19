/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingClass
public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingCodimZero
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingStep
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Claim 71.2 for the stage functors of the tower

Kollár's Claim 71.2 [Kol07, Claim 71.2]: for a closed embedding `τ : Y ↪ X` of smooth schemes with
`τ_*(𝒪_Y/J) = 𝒪_X/I`, `BMO_1(X, I, 1, ∅) = τ_* BMO_1(Y, J, 1, ∅)`. Kollár proves it [Kol07, 108] by
a chain of hypersurfaces, locally on `X`. Here the chain is walked by induction on the stage `n` of
the tower (`tower_bmo_one_eq_pushforward_closedEmbedding_aux`): at stage `0` both sides are empty
(`seq_eq_pushforward_of_hasDimLE_zero`); at stage `n + 1`, when `Y` is nowhere dense
(`max-ord(ker j) ≤ 1`) one step of the chain — a smooth hypersurface `H ⊂ X'` containing `Y'` on a
surjective coproduct of open subschemes — reduces to the hypersurface case
(`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingHypersurface`) and to the stage `n`
(`seq_eq_pushforward_of_maxOrd_ker_le_one`); otherwise a component of `X` lies inside `Y` and the
two-hypersurface argument in `X ×_k 𝔸¹` settles the identity directly
(`seq_eq_pushforward_of_not_maxOrd_ker_le_one`,
`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingCodimZero`).

The identity at any stage `n` over any base of the tower is the induction's statement
`tower_bmo_one_eq_pushforward_closedEmbedding_aux` itself; its clause form
`tower_bmo_one_commutesWithClosedEmbeddingsOfEmptyDivisor` (the predicate
`OrderGeSeqAssignment.CommutesWithClosedEmbeddingsOfEmptyDivisor`) follows.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Hironaka.Sequence Hironaka.Snc

namespace Hironaka.Stage

variable {k : Type u} [Field k] [CharZero k]

/-- The induction on the stage behind [Kol07, 108]: Claim 71.2 for the stage-`n` functor of the
tower, every `n`, every base — stage `0` by `seq_eq_pushforward_of_hasDimLE_zero`; stage `n + 1` by
`seq_eq_pushforward_of_maxOrd_ker_le_one` (one step of the chain, then the stage `n`) when `Y` is
nowhere dense, and by `seq_eq_pushforward_of_not_maxOrd_ker_le_one` when a component of `X` lies
inside `Y`. -/
theorem tower_bmo_one_eq_pushforward_closedEmbedding_aux (base : OrderReductionStage.{u} 0)
    (n : ℕ) : ∀ (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j]
      (hj : MarkedTriple.ClosedEmbedding TX TY j), IsEmpty TX.E.ι →
      ∀ hTX : TX.BMOClass n 1,
        (((tower base n).bmo 1).functor k).seq TX hTX =
          ((((tower base n).bmo 1).functor k).seq TY
            (bmoClass_of_closedEmbedding hj hTX)).pushforward j := by
  induction n with
  | zero =>
    intro TX TY j _ hj _ hTX
    exact seq_eq_pushforward_of_hasDimLE_zero base TX TY j hj hTX
  | succ n ih =>
    intro TX TY j _ hj hE hTX
    by_cases hK : j.ker.maxOrd ≤ ((1 : ℕ) : ℕ∞)
    · exact seq_eq_pushforward_of_maxOrd_ker_le_one base ih TX TY j hj hE hTX hK
    · exact seq_eq_pushforward_of_not_maxOrd_ker_le_one base TX TY j hj hE hTX hK

/-- Claim 71.2 as the predicate `OrderGeSeqAssignment.CommutesWithClosedEmbeddingsOfEmptyDivisor`
([Kol07, 34.3]): the stage-`n` functor `BMO_{n,1}` of the tower commutes with closed embeddings of
triples with empty boundary (the class proof of `Y` is arbitrary by proof irrelevance). -/
theorem tower_bmo_one_commutesWithClosedEmbeddingsOfEmptyDivisor
    (base : OrderReductionStage.{u} 0) (n : ℕ) :
    (((tower base n).bmo 1).functor k).CommutesWithClosedEmbeddingsOfEmptyDivisor :=
  fun TX TY j _ hj hE hX _ =>
    tower_bmo_one_eq_pushforward_closedEmbedding_aux base n TX TY j hj hE hX

end Hironaka.Stage
