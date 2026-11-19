/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNil
import Hironaka.Scheme.BlowUpSequence.ConcatMarked
import Hironaka.Scheme.BlowUpSequence.MarkedMono
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (a) of Włodarczyk's Theorem 1.0.2: the modified run is a smooth blow-up sequence

The embedded desingularization sequence `BED(X, I_Y, ∅)`
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) is a concatenation of truncations of runs of
`BMO_1` on marked triples of mark `1`: the run on the original triple, truncated before the
absorbing blow-up, then the loop on the isolated triple — the induced triple at the truncation's end
with its ideal enlarged to the colon by the absorbed components. Each run is a smooth blow-up
sequence of order `≥ 1` for its own marked triple ([Kol07, Theorem 69 (1)],
`isOrderGeSeq_bmoOneRun`); the truncation keeps that (`isOrderGeSeq_take`); the concatenation keeps
it when the tail is one for the induced data (`isOrderGeSeq_concat`); and enlarging the ideal only
lowers the order along the centres (`isOrderGeSeq_of_le`: the colon contains the ideal). Hence, by
strong induction on the number of members, **`BED(X, I_Y, ∅)` is a smooth blow-up sequence of order
`≥ 1` starting with `(X, I_Y, 1, ∅)`** (`isOrderGeSeq_BED`, in the sense of [Kol07, Definition 66]):
every centre is smooth (`BED_center_smooth`), has simple normal crossings with the total transform
of the boundary at its stage (`BED_hasSncWith_center`), and the total transforms are snc at every
stage (`BED_isSnc_totalTransformSeq`, `IsOrderGeSeq.isSnc_totalTransformSeq`) — clause (a) of
[Wlo05, Theorem 1.0.2] and the smoothness of the centres.

The three theorems take the hypotheses of the theorem — empty boundary, reduced `Y` — and are the
forms used by `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- **The loop is a smooth blow-up sequence of order `≥ 1` starting with `(X, I, 1, E)`**
([Kol07, Definition 66]; [Kol07, Theorem 69 (1)]) — by strong induction on the number of members:
the run truncated before the absorbing blow-up is one (`isOrderGeSeq_take`), the loop on the
isolated triple is one for the induced data with the enlarged ideal (the induction hypothesis with
`isOrderGeSeq_of_le`, the colon containing the ideal), and the concatenation is one
(`isOrderGeSeq_concat`); without an absorption the loop is the run itself. -/
theorem isOrderGeSeq_bedAux :
    ∀ (N : ℕ) (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData), C.card = N →
      (bedAux T hm C).IsOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I 1 T.E := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T₀ hm C hcard
  obtain ⟨T, m⟩ := T₀
  have h1 : m = 1 := hm
  subst h1
  classical
  have hrun : (bmoOneRun ⟨T, 1⟩ hm).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
    isOrderGeSeq_bmoOneRun ⟨T, 1⟩ hm
  by_cases h : ∃ n, HasAbsorptionAt ⟨T, 1⟩ hm C n
  · rw [bedAux_of_exists ⟨T, 1⟩ hm C h]
    have hS : ((bmoOneRun ⟨T, 1⟩ hm).take (Nat.find h)).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1
        T.E :=
      isOrderGeSeq_take _ _ _ _ hrun (Nat.find h)
    have hlt : (remainingComponents ⟨T, 1⟩ hm C (Nat.find h)).card < N := by
      rw [← hcard]
      exact card_remainingComponents_lt ⟨T, 1⟩ hm C h
    have hT := ih _ hlt (isolatedTriple ⟨T, 1⟩ hm C (Nat.find h)) (isolatedTriple_m ⟨T, 1⟩ hm C _)
      (remainingComponents ⟨T, 1⟩ hm C (Nat.find h)) rfl
    refine isOrderGeSeq_concat (T.X.left ↘ Spec (.of k)) _ _ hS ?_
    have hle : ((bmoOneRun ⟨T, 1⟩ hm).take (Nat.find h)).markedTransformSeq T.I 1 (Fin.last _) ≤
        (isolatedTriple ⟨T, 1⟩ hm C (Nat.find h)).I :=
      Scheme.IdealSheafData.le_colon_self _ _
    exact isOrderGeSeq_of_le _ hT hle
  · rw [bedAux_of_not_exists ⟨T, 1⟩ hm C h]
    exact hrun

/-- **The modified run `BED(X, I_Y, ∅)` is a smooth blow-up sequence of order `≥ 1` starting with
`(X, I_Y, 1, ∅)`** ([Wlo05, Theorem 1.0.2 (a)]; [Kol07, Definition 66]). -/
theorem isOrderGeSeq_BED (T : Triple k) :
    (BED T).IsOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I 1 T.E :=
  isOrderGeSeq_bedAux _ ⟨T, 1⟩ rfl (componentIdeals T) rfl

/-! ### The three clauses -/

/-- Every centre of `BED(X, I_Y, ∅)` is smooth over `k` — Włodarczyk's "blow-ups `σᵢ` of smooth
centers `C_{i−1}`" [Wlo05, Theorem 1.0.2]. -/
theorem BED_center_smooth (TX : Triple k) (_hE : IsEmpty TX.E.ι) :
    ∀ i : Fin (BED TX).length,
      Smooth (((BED TX).center i).subschemeι ≫ (BED TX).stageMap i.castSucc ≫
        (TX.X.left ↘ Spec (CommRingCat.of k))) :=
  (isOrderGeSeq_BED TX).1

/-- The total transform of the boundary at every stage of `BED(X, I_Y, ∅)` is snc
(`IsOrderGeSeq.isSnc_totalTransformSeq`) — the first part of clause (a) of
[Wlo05, Theorem 1.0.2]. -/
theorem BED_isSnc_totalTransformSeq (TX : Triple k) (_hE : IsEmpty TX.E.ι) :
    ∀ i : Fin ((BED TX).length + 1), ((BED TX).totalTransformSeq TX.E i).IsSnc := by
  obtain ⟨n, hn⟩ := TX.smoothOfRelativeDimension
  exact fun i => IsOrderGeSeq.isSnc_totalTransformSeq (TX.X.left ↘ Spec (.of k)) n
    (isOrderGeSeq_BED TX) TX.isSnc i

/-- Every centre has simple normal crossings with the total transform at its stage — the second
part of clause (a) of [Wlo05, Theorem 1.0.2], "`Cᵢ` has simple normal crossings with `Eᵢ`". -/
theorem BED_hasSncWith_center (TX : Triple k) (_hE : IsEmpty TX.E.ι) :
    ∀ i : Fin (BED TX).length,
      ((BED TX).totalTransformSeq TX.E i.castSucc).HasSncWith ((BED TX).center i) :=
  fun i => ((isOrderGeSeq_BED TX).2 i).1

end Hironaka.Resolution
