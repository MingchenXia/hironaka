/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The marked transform of a smaller ideal is contained in the birational transform

In the proof of Theorem 107, "if `ord N(I) ≥ m`, we can apply order reduction (68) to `N(I)`,
until its order drops below `m`" [Kol07, 111, Step 1]: a round of order reduction for the
nonmonomial part `N(I)` at `d = max-ord N(I) ≥ m` is a sequence of order `d ≥ m` for `N(I)`,
hence of order `≥ m` for `(I, m)`, since `ord_Z I ≥ ord_Z N(I)`. At the later stages of the round
the center `Z_i` has `ord_{Z_i} J_i = d` for the birational transform `J_i` of `J = N(I)`, and the
marked transform `I_i` of `(I, m)` must have `ord_{Z_i} I_i ≥ m`; this module supplies the
per-stage inclusion `I_i ⊆ J_i`. One step is
`π^{-1}_*(I, m) = (π^* I : F^m) ⊆ (π^* J : F^m) ⊆ (π^* J : F^d) = π^{-1}_* J` for `I ⊆ J`,
`m ≤ d = ord_Z J` (the colon is monotone in the ideal and antitone in the divisor; the birational
transform of `J` is its marked transform at the exact order `d`,
`weakTransform_eq_markedTransform_of_smooth`), and `ord_{Z_i} I_i ≥ ord_{Z_i} J_i = d ≥ m`
follows because the order is antitone in the ideal.

* `markedTransform_le_weakTransform_of_le`: one blow-up.
* `markedTransformSeq_le_weakTransformSeq_of_le`: along a smooth blow-up sequence of order `d`
  for `J`, at every stage.
* `isOrderGeSeq_of_isOrderSeq_of_le`: a smooth blow-up sequence of order `d ≥ m` for `(X, J, E)`
  is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` whenever `I ⊆ J` (same centers,
  same boundaries).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- For `I ⊆ J`, `m ≤ d` and a smooth center `D` with `ord_D J = d`, the marked transform
`π^{-1}_*(I, m) = (π^* I : F^m)` of [Kol07, Definition 60] is contained in the birational
transform `π^{-1}_* J = (π^* J : F^d)` of [Kol07, 58]. -/
theorem markedTransform_le_weakTransform_of_le {I J : X.IdealSheafData} {m d : ℕ} (hmd : m ≤ d)
    (D : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)] (hord : J.OrdAlongEq D.support (d : ℕ∞))
    (hIJ : I ≤ J) : I.markedTransform D m ≤ J.weakTransform D := by
  rw [weakTransform_eq_markedTransform_of_smooth f n D J hord]
  calc I.markedTransform D m
      = (I.comap D.blowUpπ).colon (D.exceptionalDivisor ^ m) := rfl
    _ ≤ (J.comap D.blowUpπ).colon (D.exceptionalDivisor ^ m) :=
        colon_mono_left _ _ _ (comap_mono _ hIJ)
    _ ≤ (J.comap D.blowUpπ).colon (D.exceptionalDivisor ^ d) :=
        colon_anti_right _ fun _ => Ideal.pow_le_pow_right hmd
    _ = J.markedTransform D d := rfl

include n in
/-- Along a smooth blow-up sequence of order `d ≥ m` for `(X, J, E)`, the marked transforms of
`(I, m)` are contained in the birational transforms of `J` at every stage whenever `I ⊆ J`; the
per-stage form of "`ord_Z I ≥ ord_Z N(I)`" in [Kol07, 111, Step 1]. -/
theorem markedTransformSeq_le_weakTransformSeq_of_le {I J : X.IdealSheafData} {E : DivisorFamily X}
    {m d : ℕ} (hmd : m ≤ d) {S : BlowUpSequence X} (hS : S.IsOrderSeq f J E d) (hIJ : I ≤ J)
    (i : Fin (S.length + 1)) : S.markedTransformSeq I m i ≤ S.weakTransformSeq J i := by
  induction S with
  | nil Y => exact hIJ
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, ht⟩ := (isOrderSeq_cons_iff f J E d D rest).1 hS
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · exact hIJ
    · have := hD
      exact ih (D.blowUpπ ≫ f) ht (markedTransform_le_weakTransform_of_le f n
          hmd D hord hIJ)
        ⟨j, Nat.lt_of_succ_lt_succ hi⟩

include n in
/-- A smooth blow-up sequence of order `d ≥ m` for `(X, J, E)` is a smooth blow-up sequence of
order `≥ m` for `(X, I, m, E)` whenever `I ⊆ J`: the same centers, smooth and with simple normal
crossings with the same boundaries, and `ord_{Z_i} I_i ≥ ord_{Z_i} J_i = d ≥ m` at every stage by
the per-stage inclusion. This is how the order reduction of `N(I)` in [Kol07, 111, Step 1] is a
sequence of order `≥ m` for `(I, m)`. -/
theorem isOrderGeSeq_of_isOrderSeq_of_le {I J : X.IdealSheafData} {E : DivisorFamily X} {m d : ℕ}
    (hmd : m ≤ d) {S : BlowUpSequence X} (hS : S.IsOrderSeq f J E d) (hIJ : I ≤ J) :
    S.IsOrderGeSeq f I m E :=
  ⟨hS.1, fun i => ⟨(hS.2 i).1, fun η hη =>
    calc (m : ℕ∞) ≤ d := by exact_mod_cast hmd
      _ = (S.weakTransformSeq J i.castSucc).ord η := ((hS.2 i).2 η hη).symm
      _ ≤ (S.markedTransformSeq I m i.castSucc).ord η :=
        ord_anti (markedTransformSeq_le_weakTransformSeq_of_le f n hmd hS hIJ i.castSucc) η⟩⟩

end AlgebraicGeometry
