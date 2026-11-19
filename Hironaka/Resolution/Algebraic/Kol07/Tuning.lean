/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Algebra.Local.CohenIso
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tuning of ideals: the converse direction of Theorem 100

Kollár's first tuning theorem [Kol07, Theorem 100] says that for `I^s ⊆ J ⊆ W_{ms}(I)` a smooth
blow-up sequence is of order `≥ m` for `(X, I, m)` iff it is of order `≥ ms` for `(X, J, ms)`. This
module proves the converse direction (a sequence of order `≥ ms` for `(X, J, ms)` is of order `≥ m`
for `(X, I, m)`), which uses only `I^s ⊆ J`; the boundary `E` is carried along.

* **Powers under the marked transform.** With `π_*^{-1}(I, m) = (π^* I : F^m)` (the colon form of
  the marked transform of [Kol07, Definition 60]),
  `(π^* I : F^m)^s · F^{ms} = ((π^* I : F^m) · F^m)^s ⊆ (π^* I)^s = π^*(I^s)`, so
  `π_*^{-1}(I, m)^s ⊆ π_*^{-1}(I^s, ms)` for every `I`, `m`, `s` (`pow_markedTransform_le`). When
  `F^m ∣ π^* I` (Kollár's `m ≤ ord_D I`) the colon is an honest quotient,
  `F^m · (π^* I : F^m) = π^* I`, so `F^{ms} · π_*^{-1}(I, m)^s = π^*(I^s)`, and the uniqueness of
  the quotient by the invertible `F^{ms}` gives equality (`markedTransform_pow`). Along a sequence,
  `I^s ⊆ J` propagates to `I_i^s ⊆ J_i` at every stage by induction, the step being the
  one-blow-up inclusion followed by the monotonicity of the marked transform in its ideal
  (`pow_markedTransformSeq_le`, Kollár's `I_{r−1}^s ⊆ J_{r−1}`); on a sequence of order `≥ m` for
  `(X, I, m, E)` every `F_{i+1}^m ∣ π_i^* I_i`, so the equality propagates too
  (`markedTransformSeq_pow`, Kollár's `I_{r−1}^s = (Π_{r−1})_*^{-1} I^s`).
* **The order at the center.** At a point `η` of a scheme smooth over a field `k` of
  characteristic zero the stalk `𝒪_{X,η}` is a regular local ring containing `ℚ`, so the order is
  multiplicative on its elements and `ord_η (I^s) = s · ord_η I` (`ord_pow`). Hence `ord_Z J ≥ ms`
  and `I^s ⊆ J` give `s · ord_η I = ord_η (I^s) ≥ ord_η J ≥ ms` at every generic point `η` of `Z`
  (the order is antitone in the ideal, [Kol07, Definition 59 (1)]), and cancelling `s ≥ 1` in `ℕ∞`
  gives `ord_Z I ≥ m` (`leOrdAlong_of_pow_le`).
* **The direction assembled.** For a sequence of order `≥ ms` for `(X, J, ms, E)`: the smoothness
  and normal crossing clauses of [Kol07, Definition 66] do not mention the ideal, and at every
  stage `I_i^s ⊆ J_i` turns `ord_{Z_i} J_i ≥ ms` into `ord_{Z_i} I_i ≥ m`, the stage `X_i` being
  smooth over `k` of the same relative dimension, so the sequence is of order `≥ m` for
  `(X, I, m, E)` (`tuning_mpr`). Kollár's induction on the length of the sequence is the induction
  inside `pow_markedTransformSeq_le`; the order clauses are then read off stage by stage.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Powers under the marked transform -/

section PowerTransform

variable (D I J : X.IdealSheafData) (m s : ℕ)

/-- `π_*^{-1}(I, m)^s ⊆ π_*^{-1}(I^s, ms)` (the proof of the converse in [Kol07, Theorem 100]),
since `(π^* I : F^m)^s · F^{ms} = ((π^* I : F^m) · F^m)^s ⊆ (π^* I)^s = π^*(I^s)`. -/
theorem pow_markedTransform_le :
    I.markedTransform D m ^ s ≤ (I ^ s).markedTransform D (m * s) := by
  change ((I.comap D.blowUpπ).colon (D.exceptionalDivisor ^ m)) ^ s ≤
    ((I ^ s).comap D.blowUpπ).colon (D.exceptionalDivisor ^ (m * s))
  rw [Scheme.IdealSheafData.le_colon_iff_mul_le, comap_pow, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ bot_le (colon_mul_le _ _) s

/-- When `F^m ∣ π^* I` (Kollár's `m ≤ ord_D I`, under which [Kol07, Definition 60] defines
`π_*^{-1}(I, m)`), `π_*^{-1}(I^s, ms) = π_*^{-1}(I, m)^s`: indeed
`F^{ms} · π_*^{-1}(I, m)^s = (F^m · π_*^{-1}(I, m))^s = π^*(I^s)`, and the quotient by the
invertible `F^{ms}` is unique. -/
theorem markedTransform_pow (h : D.exceptionalDivisor ^ m ∣ I.comap D.blowUpπ) :
    (I ^ s).markedTransform D (m * s) = I.markedTransform D m ^ s := by
  have hF : D.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π D
  change ((I ^ s).comap D.blowUpπ).colon (D.exceptionalDivisor ^ (m * s)) =
    ((I.comap D.blowUpπ).colon (D.exceptionalDivisor ^ m)) ^ s
  refine colon_pow_eq_of_mul_eq (I := (I ^ s).comap D.blowUpπ) hF (m * s) _ ?_
  rw [comap_pow, pow_mul, ← mul_pow, pow_mul_colon_of_dvd _ _ m h]

/-- "Since `I^s ⊂ J`, we know that `I_{r−1}^s ⊂ J_{r−1}`" (the proof of the converse in
[Kol07, Theorem 100]): by induction on the sequence, the step being the one-blow-up inclusion
`pow_markedTransform_le` followed by the monotonicity of the marked transform in its ideal
(`markedTransform_mono`). -/
theorem pow_markedTransformSeq_le (S : BlowUpSequence X) (hIJ : I ^ s ≤ J)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq I m i ^ s ≤ S.markedTransformSeq J (m * s) i := by
  induction S with
  | nil Y => exact hIJ
  | cons Y D rest ih =>
    rcases i with ⟨_ | i, hi⟩
    · exact hIJ
    · exact ih (I.markedTransform D m) (J.markedTransform D (m * s))
        ((pow_markedTransform_le D I m s).trans (markedTransform_mono D hIJ (m * s)))
        ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end PowerTransform

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

section Sequence

variable (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) (m s : ℕ)

include n

/-- `I_{r−1}^s = (Π_{r−1})_*^{-1} I^s` (the proof of the converse in [Kol07, Theorem 100]): along a
smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, every `F_{i+1}^m ∣ π_i^* I_i`
(`pow_dvd_comap_of_leOrdAlong` at each stage), so the one-blow-up equality `markedTransform_pow`
propagates by induction on the sequence. -/
theorem markedTransformSeq_pow (h : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    S.markedTransformSeq (I ^ s) (m * s) i = S.markedTransformSeq I m i ^ s := by
  induction S with
  | nil Y => rfl
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | i, hi⟩
    · rfl
    · change rest.markedTransformSeq ((I ^ s).markedTransform D (m * s)) (m * s)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩ =
        rest.markedTransformSeq (I.markedTransform D m) m ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ^ s
      rw [markedTransform_pow D I m s (pow_dvd_comap_of_leOrdAlong f n D I hm)]
      exact ih (D.blowUpπ ≫ f) (I.markedTransform D m) (E.totalTransform D) ht
        ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end Sequence

/-! ### The order at the center -/

section Pointwise

variable (I J : X.IdealSheafData) (m s : ℕ)

include f n

/-- At every point `η` of a scheme smooth over a field of characteristic zero,
`ord_η (I^s) = s · ord_η I` for `s ≥ 1` (the pointwise form of `cosupp(I, m) = cosupp(I^c, mc)`,
[Kol07, Definition 59 (3)]). The stalk `𝒪_{X,η}` is a regular local ring
(`isRegularLocalRing_stalk`) containing `ℚ` (`f.stalkAlgebraRat η`), so the order is
multiplicative on its elements (`ordElem_mul_of_algebraRat`) and `ord_pow_of_ordElem_mul` applies
to the stalk ideal `I_η`, whose `s`-th power is the stalk of `I^s`. -/
theorem ord_pow (hs : 1 ≤ s) (η : X) : (I ^ s).ord η = (s : ℕ∞) * I.ord η := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := isRegularLocalRing_stalk f η
  let _ := f.stalkAlgebraRat η
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, stalkIdeal_pow]
  exact IsLocalRing.ord_pow_of_ordElem_mul
    (IsLocalRing.ordElem_mul_of_algebraRat (X.presheaf.stalk η)) _ hs

/-- "If `ord_Z J_{r−1} ≥ ms`, then `ord_Z I_{r−1} ≥ m`" (the proof of the converse in
[Kol07, Theorem 100]): at each generic point `η` of `Z`,
`ms ≤ ord_η J ≤ ord_η (I^s) = s · ord_η I` (the order is antitone in the ideal, `ord_anti`, for the
middle step), and `s ≥ 1` cancels in `ℕ∞`. -/
theorem leOrdAlong_of_pow_le (Z : Closeds X) (hs : 1 ≤ s) (hIJ : I ^ s ≤ J)
    (hJ : J.LeOrdAlong Z ((m * s : ℕ) : ℕ∞)) : I.LeOrdAlong Z (m : ℕ∞) := by
  intro η hη
  have h1 : ((m * s : ℕ) : ℕ∞) ≤ (I ^ s).ord η := (hJ η hη).trans (ord_anti hIJ η)
  rw [ord_pow f n I s hs η, Nat.cast_mul, mul_comm (m : ℕ∞) (s : ℕ∞)] at h1
  exact (ENat.mul_le_mul_left_iff (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hs))
    (ENat.natCast_ne_top s)).mp h1

end Pointwise

/-! ### The direction assembled -/

section Assemble

variable (S : BlowUpSequence X) (I J : X.IdealSheafData) (E : DivisorFamily X) (m s : ℕ)

include n

/-- The converse direction of [Kol07, Theorem 100]: a smooth blow-up sequence of order `≥ ms` for
`(X, J, ms, E)` with `I^s ⊆ J`, `s ≥ 1`, is of order `≥ m` for `(X, I, m, E)`. The smoothness and
normal crossing clauses of Definition 66 are inherited, and at every stage `i` the order clause
`ord_{Z_i} I_i ≥ m` follows from `I_i^s ⊆ J_i` (`pow_markedTransformSeq_le`) and
`ord_{Z_i} J_i ≥ ms` (`leOrdAlong_of_pow_le`), the stage `X_i` being smooth of relative dimension
`n` over `k` (`IsSmooth.smoothOfRelativeDimension_stageMap`). -/
theorem tuning_mpr (hs : 1 ≤ s) (hIJ : I ^ s ≤ J) (h : S.IsOrderGeSeq f J (m * s) E) :
    S.IsOrderGeSeq f I m E := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  have _ := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) h.1 i.castSucc
  exact leOrdAlong_of_pow_le (S.stageMap i.castSucc ≫ f) n _ _ m s (S.center i).support hs
    (pow_markedTransformSeq_le I J m s S hIJ i.castSucc) (IsOrderGeSeq.leOrdAlong h i)

end Assemble

end Hironaka.Sequence
