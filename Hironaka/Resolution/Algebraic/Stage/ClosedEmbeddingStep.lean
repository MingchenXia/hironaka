/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingCover
public import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingClass
public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingHypersurface
import Hironaka.Resolution.Algebraic.Stage.Coherence
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Scheme.BlowUpSequence.EqNilMarked
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Lean.Message

/-!
# Claim 71.2: the induction step through a hypersurface

Kollár's proof of Claim 71.2 [Kol07, 108] reduces, locally on `X`, to a chain of hypersurfaces
`Y = Y₀ ⊂ Y₁ ⊂ ⋯ ⊂ Y_c = X` and treats one hypersurface at a time. Here the chain is walked by
**induction on the stage** of the tower: at stage `n + 1`, one step of the chain
(`HypersurfaceCover`, a smooth hypersurface `H ⊂ X'` containing `Y'` on a surjective coproduct of
open subschemes) reduces the identity for `Y ⊂ X` to the hypersurface case for `H ⊂ X'`
(`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingHypersurface`) and to the identity for `Y' ⊂ H`
**at stage `n`** (`dim H ≤ n`, the coherence of the tower moving the value between the stages), then
descends along the cover. This module holds:

* `seq_eq_pushforward_of_isEmpty` — the trivial case `Y = ∅`: then `J = 𝒪_Y`, `I = 𝒪_X`, and both
  sides are the empty sequence (every stage).
* `seq_eq_pushforward_of_hasDimLE_zero` — the base of the induction, stage `0`: both sides are empty
  (`seq_eq_nil_of_hasDimLE_zero`).
* `seq_eq_pushforward_of_hypersurfaceCover` — the induction step: given the identity at stage `n`
  for every closed embedding of marked triples with `E = ∅`, and a hypersurface cover of `Y ⊂ X`,
  the identity holds for `Y ⊂ X` at stage `n + 1`.
* `seq_eq_pushforward_of_maxOrd_ker_le_one` — the step assembled with the cover's existence: for `Y`
  nowhere dense (`max-ord(ker j) ≤ 1`) the identity at stage `n + 1` follows from the identity at
  stage `n`.

The remaining case of the induction step — `max-ord(ker j) = ⊤`, a component of `X` inside `Y` — is
`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingCodimZero`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Snc

namespace Hironaka.Stage

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- The boundary case `Y = ∅` of Claim 71.2, at every stage: with `Y` empty, `J = 𝒪_Y` and
`I = τ_* J = 𝒪_X`, so both `BMO_1(X, I, 1, ∅)` and `τ_* BMO_1(Y, J, 1, ∅)` are the empty sequence
(`eq_nil_of_isOrderGeSeq_of_maxOrd_lt`, `pushforward_nil`). -/
theorem seq_eq_pushforward_of_isEmpty (base : OrderReductionStage.{u} 0) (n : ℕ)
    (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j]
    (hj : MarkedTriple.ClosedEmbedding TX TY j) (hTX : TX.BMOClass n 1) (hY : IsEmpty TY.X.left) :
    (((tower base n).bmo 1).functor k).seq TX hTX =
      ((((tower base n).bmo 1).functor k).seq TY
        (bmoClass_of_closedEmbedding hj hTX)).pushforward j := by
  have hTYtop : TY.I = ⊤ := Hironaka.BD.eq_top_of_maxOrd_le_zero TY.I
    (Hironaka.BO.maxOrd_eq_zero_of_isEmpty TY.I).le
  have hTXtop : TX.I = ⊤ := by rw [hj.1.2.1, hTYtop, Scheme.IdealSheafData.map_top]
  have h0 : ∀ {Z : Scheme.{u}} (I : Z.IdealSheafData), I = ⊤ → I.maxOrd < ((1 : ℕ) : ℕ∞) := by
    intro Z I hI
    rw [hI]
    exact lt_of_le_of_lt ((Scheme.IdealSheafData.maxOrd_le_iff _).mpr fun x =>
        by rw [Scheme.IdealSheafData.ord_top]) (by norm_num)
  have hL : (((tower base n).bmo 1).functor k).seq TX hTX = nil TX.X.left :=
    eq_nil_of_isOrderGeSeq_of_maxOrd_lt (TX.X.left ↘ Spec (.of k))
      ((((tower base n).bmo 1).functor k).isOrderGeSeq TX hTX)
      ((((tower base n).bmo 1).functor k).noEmptyCenters TX hTX)
      (by rw [hTX.2.2]; exact h0 TX.I hTXtop)
  have hR : (((tower base n).bmo 1).functor k).seq TY (bmoClass_of_closedEmbedding hj hTX) =
      nil TY.X.left :=
    eq_nil_of_isOrderGeSeq_of_maxOrd_lt (TY.X.left ↘ Spec (.of k))
      ((((tower base n).bmo 1).functor k).isOrderGeSeq TY _)
      ((((tower base n).bmo 1).functor k).noEmptyCenters TY _)
      (by rw [hj.2, hTX.2.2]; exact h0 TY.I hTYtop)
  rw [hL, hR, pushforward_nil]

/-- The base of the induction ([Kol07, 70], dimension `0`): at stage `0` both sides of Claim 71.2
are the empty sequence. -/
theorem seq_eq_pushforward_of_hasDimLE_zero (base : OrderReductionStage.{u} 0)
    (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j]
    (hj : MarkedTriple.ClosedEmbedding TX TY j) (hTX : TX.BMOClass 0 1) :
    (((tower base 0).bmo 1).functor k).seq TX hTX =
      ((((tower base 0).bmo 1).functor k).seq TY
        (bmoClass_of_closedEmbedding hj hTX)).pushforward j := by
  rw [OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ TX hTX hTX.2.1 hTX.2.2.ge,
    OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ TY _ (bmoClass_of_closedEmbedding hj hTX).2.1
      (bmoClass_of_closedEmbedding hj hTX).2.2.ge, pushforward_nil]

/-- One step of the chain of [Kol07, 108]: given the identity of Claim 71.2 at stage `n` for every
closed embedding of marked triples with `E = ∅`, and a hypersurface cover of `Y ⊂ X` (a smooth
hypersurface `H ⊂ X'` containing `Y'` on a surjective coproduct of open subschemes `X' → X`), the
identity holds for `Y ⊂ X` at stage `n + 1`: on `X'` it is the hypersurface case for `H ⊂ X'`
composed with the identity for `Y' ⊂ H` at stage `n` (`dim H ≤ n`; the values at `H` and `Y'` moved
between the stages by `tower_bmo_coherent`), push-forwards composing along `j' = ℓ ≫ (H ↪ X')`
[Kol07, Definition 30.3]; then it descends along the cover (`seq_eq_pushforward_of_cover`). -/
theorem seq_eq_pushforward_of_hypersurfaceCover (base : OrderReductionStage.{u} 0) {n : ℕ}
    (ih : ∀ (TX₀ TY₀ : MarkedTriple k) (j₀ : TY₀.X.left ⟶ TX₀.X.left) [IsClosedImmersion j₀]
      (hj₀ : MarkedTriple.ClosedEmbedding TX₀ TY₀ j₀), IsEmpty TX₀.E.ι →
      ∀ hTX₀ : TX₀.BMOClass n 1,
        (((tower base n).bmo 1).functor k).seq TX₀ hTX₀ =
          ((((tower base n).bmo 1).functor k).seq TY₀
            (bmoClass_of_closedEmbedding hj₀ hTX₀)).pushforward j₀)
    (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j]
    (hj : MarkedTriple.ClosedEmbedding TX TY j) (hTX : TX.BMOClass (n + 1) 1)
    (c : HypersurfaceCover n TX TY j) :
    (((tower base (n + 1)).bmo 1).functor k).seq TX hTX =
      ((((tower base (n + 1)).bmo 1).functor k).seq TY
        (bmoClass_of_closedEmbedding hj hTX)).pushforward j := by
  have := c.smooth_g
  have := c.isClosedImmersion_j'
  have := c.smooth_hS
  have := c.isClosedImmersion_Hι
  have := c.isClosedImmersion_ℓ
  -- the classes of the cover's triples
  have hTX' : c.TX'.BMOClass (n + 1) 1 := ⟨le_rfl, c.hasDimLE_X', c.pullback_TX'.2.trans hTX.2.2⟩
  have hTH' : c.TH'.BMOClass (n + 1) 1 := bmoClass_of_closedEmbedding c.closedEmbedding_X' hTX'
  have hTH'n : c.TH'.BMOClass n 1 := ⟨le_rfl, c.hasDimLE_H, hTH'.2.2⟩
  have hTY' : c.TY'.BMOClass (n + 1) 1 := bmoClass_of_closedEmbedding c.closedEmbedding_H hTH'
  have hTY'n : c.TY'.BMOClass n 1 := bmoClass_of_closedEmbedding c.closedEmbedding_H hTH'n
  have hEH : IsEmpty c.TH'.E.ι := by
    rw [c.closedEmbedding_X'.1.2.2]
    exact c.isEmpty_E'
  -- the identity on `X'`: the hypersurface case for `H ⊂ X'`, then stage `n` for `Y' ⊂ H`
  have h1 := tower_bmo_one_eq_pushforward_of_isSmoothDivisor_ker base c.TX' c.TH' c.Hι
    c.closedEmbedding_X' c.isEmpty_E' hTX' c.isSmoothDivisor_ker
  have h2 := ih c.TH' c.TY' c.ℓ c.closedEmbedding_H hEH hTH'n
  have hcohH := tower_bmo_coherent base 1 (Nat.le_succ n) c.TH'
    (bmoClass_of_closedEmbedding c.closedEmbedding_X' hTX') hTH'n
  have hcohY := tower_bmo_coherent base 1 (Nat.le_succ n) c.TY' hTY'
    (bmoClass_of_closedEmbedding c.closedEmbedding_H hTH'n)
  have h' : (((tower base (n + 1)).bmo 1).functor k).seq c.TX' hTX' =
      ((((tower base (n + 1)).bmo 1).functor k).seq c.TY' hTY').pushforward c.j' := by
    rw [h1, hcohH, h2, hcohY, pushforward_comp]
    exact pushforward_congr _ c.fac
  -- descent along the cover
  exact seq_eq_pushforward_of_cover (((tower base (n + 1)).bmo 1).commutesWithSmooth k).1 j c.g
    c.surjective_g c.j' c.hS c.surjective_hS c.sq c.pullback_TX' c.pullback_TY' hTX
    (bmoClass_of_closedEmbedding hj hTX) hTX' hTY' h'

/-- [Kol07, 108]: for `Y` nowhere dense in `X` (`max-ord(ker j) ≤ 1`), the identity of Claim 71.2 at
stage `n + 1` follows from the identity at stage `n` — the hypersurface cover exists
(`exists_hypersurfaceCover`) and the step applies; an empty `X` is the boundary case. -/
theorem seq_eq_pushforward_of_maxOrd_ker_le_one (base : OrderReductionStage.{u} 0) {n : ℕ}
    (ih : ∀ (TX₀ TY₀ : MarkedTriple k) (j₀ : TY₀.X.left ⟶ TX₀.X.left) [IsClosedImmersion j₀]
      (hj₀ : MarkedTriple.ClosedEmbedding TX₀ TY₀ j₀), IsEmpty TX₀.E.ι →
      ∀ hTX₀ : TX₀.BMOClass n 1,
        (((tower base n).bmo 1).functor k).seq TX₀ hTX₀ =
          ((((tower base n).bmo 1).functor k).seq TY₀
            (bmoClass_of_closedEmbedding hj₀ hTX₀)).pushforward j₀)
    (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j]
    (hj : MarkedTriple.ClosedEmbedding TX TY j) (hE : IsEmpty TX.E.ι)
    (hTX : TX.BMOClass (n + 1) 1) (hK : j.ker.maxOrd ≤ ((1 : ℕ) : ℕ∞)) :
    (((tower base (n + 1)).bmo 1).functor k).seq TX hTX =
      ((((tower base (n + 1)).bmo 1).functor k).seq TY
        (bmoClass_of_closedEmbedding hj hTX)).pushforward j := by
  by_cases hne : Nonempty TX.X.left
  · obtain ⟨c⟩ := exists_hypersurfaceCover TX TY j hj hE hTX hK
    exact seq_eq_pushforward_of_hypersurfaceCover base ih TX TY j hj hTX c
  · have hY : IsEmpty TY.X.left := ⟨fun y => hne ⟨j y⟩⟩
    exact seq_eq_pushforward_of_isEmpty base (n + 1) TX TY j hj hTX hY

end Hironaka.Stage
