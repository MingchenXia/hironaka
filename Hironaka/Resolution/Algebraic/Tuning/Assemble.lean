/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.Kol07.Tuning
import Hironaka.Resolution.Algebraic.Tuning.Sequence
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tuning of ideals, I: Kollár's Theorem 100

Kollár's Theorem 100 [Kol07, Theorem 100] (Tuning of ideals, I): for a smooth variety `X`, an ideal
sheaf `I` with `m = max-ord I`, an integer `s ≥ 1` and an ideal sheaf `J` with
`I^s ⊂ J ⊂ W_{ms}(I)`, a smooth blow-up sequence is of order `≥ m` starting with `(X, I, m)` iff it
is of order `≥ ms` starting with `(X, J, ms)`. Here the theorem is stated with a divisor family `E`
carried along, as Corollary 101 needs it.

* `tuning_iff` pairs the two directions: `⟹` is `tuning_mp` of
  `Hironaka.Resolution.Algebraic.Tuning.Sequence`, which uses only `J ⊂ W_{ms}(I)`; `⟸` is
  `tuning_mpr` of `Hironaka.Resolution.Algebraic.Kol07.Tuning`, which uses only `s ≥ 1` and `I^s ⊂
  J`.
* The two bounds of the hypothesis: `J = I^s` (`tuning_iff_pow`; the inclusions are `I^s ⊆ I^s` and
  `I^s ⊆ W_{ms}(I)`, `pow_le_W`) and `J = W_{ms}(I)` (`tuning_iff_W`; `I^s ⊆ W_{ms}(I)` and
  `W_{ms}(I) ⊆ W_{ms}(I)`), the latter being the form in which the proof of [Kol07, Corollary 101]
  invokes Theorem 100.
* `W_2(I) = I + D(I)^2` (`W_two_eq`), Kollár's `W(I)` [Kol07, (54.1)], which is `W_{m!}(I)`
  [Kol07, Aside 99.10], at `m = 2`: an exponent vector `e : Fin 3 → ℕ` has weight `2e₀ + e₁ ≥ 2` iff
  `e₀ ≥ 1` (then `I^{e₀} D(I)^{e₁} D²(I)^{e₂} ⊆ I`) or `e₀ = 0` and `e₁ ≥ 2` (then it lies in
  `D(I)^2`); conversely `I` and `D(I)^2` are the generating products of `(1, 0, 0)` and `(0, 2, 0)`.
  The worked examples of `Hironaka.Balanced` compute this ideal for Kollár's Examples 11 and 106. -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  IsLocalRing

namespace Hironaka.Sequence

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-! ### `W_2(I) = I + D(I)²` -/

section TwoTwo

variable (I : X.IdealSheafData)

/-- `W_2(I) = I + D(I)^2`, Kollár's `W(I)` [Kol07, (54.1)] — which is `W_{m!}(I)`
[Kol07, Aside 99.10] — at `m = 2`: an exponent vector `(e₀, e₁, e₂)` has weight `2e₀ + e₁ ≥ 2` iff
`e₀ ≥ 1` or `e₁ ≥ 2`. -/
theorem W_two_eq : IdealSheafData.W f I 2 2 = I ⊔ IdealSheafData.derivative f I ^ 2 := by
  have hD : IdealSheafData.derivativeIter f 1 I = IdealSheafData.derivative f I := by
    rw [IdealSheafData.derivativeIter_succ, IdealSheafData.derivativeIter_zero]
  refine le_antisymm ((IdealSheafData.W_le_iff f).mpr fun e he => ?_) (sup_le ?_ ?_)
  · have hwt : wt 2 e = 2 * e 0 + e 1 := by
      simp [wt, Fin.sum_univ_three]
    rw [hwt] at he
    rw [Fin.prod_univ_three]
    by_cases h0 : e 0 = 0
    · have h1 : e 1 ≠ 0 := by omega
      refine le_sup_of_le_right ?_
      calc IdealSheafData.derivativeIter f (0 : Fin 3) I ^ e 0 * IdealSheafData.derivativeIter f
             (1 : Fin 3) I ^ e 1 *
            IdealSheafData.derivativeIter f (2 : Fin 3) I ^ e 2
          ≤ IdealSheafData.derivativeIter f (1 : Fin 3) I ^ e 1 := fun U => by
            rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
              show ((0 : Fin 3) : ℕ) = 0 from rfl, h0, pow_zero, one_mul]
            exact Ideal.mul_le_left
        _ ≤ IdealSheafData.derivativeIter f (1 : Fin 3) I ^ 2 := by
            change IdealSheafData.derivativeIter f 1 I ^ e 1 ≤ IdealSheafData.derivativeIter f 1 I
                ^ 2
            rw [hD]
            exact fun U => Ideal.pow_le_pow_right (by omega)
        _ = IdealSheafData.derivative f I ^ 2 := by
            change IdealSheafData.derivativeIter f 1 I ^ 2 = _
            rw [hD]
    · refine le_sup_of_le_left ?_
      calc IdealSheafData.derivativeIter f (0 : Fin 3) I ^ e 0 * IdealSheafData.derivativeIter f
             (1 : Fin 3) I ^ e 1 *
            IdealSheafData.derivativeIter f (2 : Fin 3) I ^ e 2
          ≤ IdealSheafData.derivativeIter f (0 : Fin 3) I ^ e 0 := fun U => by
            exact (Ideal.mul_le_left).trans Ideal.mul_le_left
        _ ≤ I := by
            change IdealSheafData.derivativeIter f 0 I ^ e 0 ≤ I
            rw [IdealSheafData.derivativeIter_zero]
            exact fun U => Ideal.pow_le_self h0
  · have h := IdealSheafData.prod_le_W f (I := I) (m := 2) (s := 2) (e := ![1, 0, 0])
      (by simp [wt, Fin.sum_univ_three])
    simpa [Fin.prod_univ_three] using h
  · have h := IdealSheafData.prod_le_W f (I := I) (m := 2) (s := 2) (e := ![0, 2, 0])
      (by simp [wt, Fin.sum_univ_three])
    simpa [Fin.prod_univ_three, hD] using h

end TwoTwo

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

/-! ### Theorem 100 -/

section Assemble

variable (S : BlowUpSequence X) (I J : X.IdealSheafData) (E : DivisorFamily X) (m s : ℕ)

include n

/-- **Kollár's Theorem 100** [Kol07, Theorem 100]: for `m = max-ord I`, `s ≥ 1` and
`I^s ⊂ J ⊂ W_{ms}(I)`, a smooth blow-up sequence is of order `≥ m` starting with `(X, I, m, E)` iff
it is of order `≥ ms` starting with `(X, J, ms, E)`; the two directions `tuning_mp` and `tuning_mpr`
paired. The hypothesis `m = max-ord I` is part of Kollár's statement and is kept so that the theorem
reads as printed and its uses in Corollary 101 supply it; the proof does not need it, because both
directions (`tuning_mp`, `tuning_mpr`) are order estimates valid for every `m`, comparing the marked
transforms of `I^s ⊆ J ⊆ W_{ms}(I)` along the sequence. -/
theorem tuning_iff (hI : I.maxOrd = m) (hs : 1 ≤ s) (hIJ : I ^ s ≤ J)
    (hJW : J ≤ IdealSheafData.W f I m (m * s)) :
    S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f J (m * s) E := by
  have _ := hI
  exact ⟨tuning_mp f n S I J E m s hJW, tuning_mpr f n S I J E m s hs hIJ⟩

end Assemble

/-! ### The two bounds -/

section Bounds

variable (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) (m s : ℕ)

include n

/-- Theorem 100 at the lower bound `J = I^s`: `(X, I, m, E)` and `(X, I^s, ms, E)` have the same
smooth blow-up sequences of order `≥ m`, respectively `≥ ms`. -/
theorem tuning_iff_pow (hI : I.maxOrd = m) (hs : 1 ≤ s) :
    S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f (I ^ s) (m * s) E :=
  tuning_iff f n S I (I ^ s) E m s hI hs le_rfl (IdealSheafData.pow_le_W f le_rfl)

/-- Theorem 100 at the upper bound `J = W_{ms}(I)`, the form invoked in the proof of
[Kol07, Corollary 101]: `(X, I, m, E)` and `(X, W_{ms}(I), ms, E)` have the same smooth blow-up
sequences of order `≥ m`, respectively `≥ ms`. -/
theorem tuning_iff_W (hI : I.maxOrd = m) (hs : 1 ≤ s) :
    S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f (IdealSheafData.W f I m (m * s)) (m * s) E :=
  tuning_iff f n S I (IdealSheafData.W f I m (m * s)) E m s hI hs
      (IdealSheafData.pow_le_W f le_rfl) le_rfl

end Bounds

end Hironaka.Sequence
