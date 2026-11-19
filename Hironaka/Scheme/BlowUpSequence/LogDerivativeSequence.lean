/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.TransformLogDerivative
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicSheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The logarithmic version of Theorem 76 along a blow-up sequence

Kollár's logarithmic version of Theorem 76, equation (87.3) of [Kol07, 87], along a smooth
blow-up sequence `B` of order `≥ m` starting with `(X, I, m, E)`, for any closed `S` (the
statements drop Kollár's hypothesis that every center lies in the strict transform `S_i` of `S`,
which the proofs do not require):
for `j ≤ m` and every stage `i`, `Π_*^{-1}(D^j(−log S)(I), m − j) ⊆ D^j(−log S_i)(Π_*^{-1}(I, m))`
(`markedTransformSeq_logDerivativeIter_le`), and the marked transforms of the logarithmic
derivative sequence are defined at every stage
(`exceptionalAt_pow_dvd_comap_step_logDerivativeIter`).

**The joint induction** (as for Theorem 76 in
`Hironaka/Scheme/BlowUpSequence/DerivativeSequence.lean`, and as in [Wlo05, Lemma 2.6.4]). Induction
on the sequence `B`: for `nil` the statement is the identity; for `cons X D rest`, at the first
stage the one-blow-up statement of `Hironaka/Scheme/BlowUpSequence/TransformLogDerivative.lean`
(`markedTransform_logDerivativeIter_le`), then the marked recursion is monotone in its starting
ideal (`markedTransformSeq_mono`) and the tail is a sequence of order `≥ m` for the transformed data
`(B_D X, π_*^{-1}(I, m), E_1)` with the hypersurface `S₁ = strictTransform D S`, to which the
induction hypothesis applies. Definedness at every stage is that of the derivative sequence
(`exceptionalAt_pow_dvd_comap_step_derivativeIter`), transported to the smaller ideals `D^j(−log
S)(I) ⊆ D^j(I)` (`logDerivativeIter_le_derivativeIter`) by the antitonicity of the order
(`ord_anti`) and the monotonicity of the marked recursion.

Convention: in the printed (87.3) the subscripts of `S` appear interchanged; here `S` is on the
left and its transform `S_i` on the right.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (B : BlowUpSequence X) (S I : X.IdealSheafData)
  (E : DivisorFamily X) (m : ℕ)

include n

/-- Equation (87.3) of [Kol07, 87] along the sequence: for a smooth blow-up sequence of order
`≥ m` starting with `(X, I, m, E)`, any closed `S`, and `j ≤ m`,
`Π_*^{-1}(D^j(−log S)(I), m − j) ⊆ D^j(−log S_i)(Π_*^{-1}(I, m))` at every stage, `S_i` the strict
transform of `S`. -/
theorem markedTransformSeq_logDerivativeIter_le (h : B.IsOrderGeSeq f I m E) {j : ℕ} (hj : j ≤ m)
    (i : Fin (B.length + 1)) :
    B.markedTransformSeq (S.logDerivativeIter f j I) (m - j) i ≤
      (B.strictTransformSeq S i).logDerivativeIter (B.stageMap i ≫ f) j
        (B.markedTransformSeq I m i) := by
  induction B with
  | nil Y =>
    change S.logDerivativeIter f j I ≤ S.logDerivativeIter (𝟙 Y ≫ f) j I
    rw [Category.id_comp]
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | i, hi⟩
    · change S.logDerivativeIter f j I ≤ S.logDerivativeIter (𝟙 Y ≫ f) j I
      rw [Category.id_comp]
    · change rest.markedTransformSeq ((S.logDerivativeIter f j I).markedTransform D (m - j)) (m - j)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≤
        (rest.strictTransformSeq (S.strictTransform D)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩).logDerivativeIter
          ((rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f) j
          (rest.markedTransformSeq (I.markedTransform D m) m ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      rw [Category.assoc]
      exact (markedTransformSeq_mono rest
        (markedTransform_logDerivativeIter_le f n D S I hm hj) (m - j) _).trans
        (ih (D.blowUpπ ≫ f) (S.strictTransform D) (I.markedTransform D m)
            (E.totalTransform D) ht
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-- The marked transform `(π_i)_*^{-1}(J_i, m − j)` of the logarithmic derivative sequence
`J_i := Π_*^{-1}(D^j(−log S)(I), m − j)` is defined at every stage in the sense of
[Kol07, Definition 60] (`F_{i+1}^{m−j}` divides `π_i^* J_i`), because `D^j(−log S)(I) ⊆ D^j(I)`
and the derivative sequence is defined (`exceptionalAt_pow_dvd_comap_step_derivativeIter`). -/
theorem exceptionalAt_pow_dvd_comap_step_logDerivativeIter (h : B.IsOrderGeSeq f I m E) {j : ℕ}
    (hj : j ≤ m) (i : Fin B.length) :
    B.exceptionalAt i ^ (m - j) ∣
      (B.markedTransformSeq (S.logDerivativeIter f j I) (m - j) i.castSucc).comap (B.step i) := by
  refine exceptionalAt_pow_dvd_comap_step_of_leOrdAlong f n B h.1 i _ fun η hη => ?_
  have hle := markedTransformSeq_mono B (logDerivativeIter_le_derivativeIter f S I j) (m - j)
    i.castSucc
  exact (IsOrderGeSeq.leOrdAlong (isOrderGeSeq_derivativeIter f n B I E m h hj) i η hη).trans
    (ord_anti hle η)

end AlgebraicGeometry
