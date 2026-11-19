/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
import Hironaka.Resolution.Algebraic.BoundaryClearing.Tuned
import Hironaka.Resolution.Algebraic.Tuning.Corollary101
import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Resolution.Algebraic.Tuning.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 1 of order reduction: properties of the tuned triple

Step 1 of the proof of [Kol07, Theorem 103] replaces the ideal `I` of a triple `(X, I, E)` with
`max-ord I = m` by the maximal coefficient ideal `W(I) = W_s(I)` of [Kol07, Corollary 101], which
is D-balanced and MC-invariant and for which order reduction is equivalent to order reduction for
`I`. This module states, for the tuned triple `T.tuned m hm = (X, W_{s(m)}(I), E)`,
what the sheaf-level theory of tuning (`Hironaka/Resolution/Algebraic/Tuning/`) gives:

* the scheme and the divisor are unchanged and the ideal is `W_{s(m)}(I)`, definitionally
  (`tuned_X`, `tuned_I`, `tuned_E`, `hasDimLE_tuned`);
* for `max-ord I = m ≥ 1`, the tuned ideal has maximal order `s(m)`, is D-balanced and
  MC-invariant with respect to `s(m)`, and a smooth blow-up sequence is of order `m` for `T` iff
  it is of order `s(m)` for the tuned triple (`maxOrd_tuned`, `isDBalanced_tuned`,
  `isMCInvariant_tuned`, `isOrderSeq_tuned_iff`; [Kol07, Theorem 100 and Corollary 101]);
* clause (1) of Theorem 103 transfers back through the tuning: along a smooth blow-up sequence of
  order `m` for `(X, I, E)`, the final transform of `W_{s(m)}(I)` has maximal order `< s(m)` iff
  that of `I` has maximal order `< m` (`maxOrd_weakTransformSeq_lt_iff_tuned`). Pointwise,
  `ord_x I_r ≥ m` iff `ord_x W_r ≥ s(m)` at the last stage; a supremum in `ℕ∞` of orders is `< s`,
  for a natural number `s ≥ 1`, iff every order is `< s` (`maxOrd_lt_iff_forall_ord_lt`), so the
  two suprema are below their marks together;
* tuning commutes with the two functoriality inputs of clause (2), the pull-back of triples along
  a smooth morphism and the change of fields ([Kol07, 34.1–34.2]), because the maximal coefficient
  ideal commutes with smooth pull-back and with base change (`isPullbackOf_tuned`,
  `isBaseChangeOf_tuned`);
* clause (1) of `BOData` read pointwise and as `cosupp(I_r, m) = ∅`
  (`BOData.ord_weakTransformSeq_lt`, `BOData.cosupp_eq_empty`), and the domain unfolded
  (`boClass_iff`);
* the order condition of [Kol07, Definition 66] for `(X, I, E)` at order `m` and for `(X, J, E)`
  at order `m'` share the smoothness and normal-crossings clauses, which are computed from the
  centres alone, so they are equivalent as soon as the order clauses `ord_{Z_i} I_i = m` and
  `ord_{Z_i} J_i = m'` are, stage by stage (`isOrderSeq_iff_of_ordAlongEq_iff`; the remark on `E`
  in the proof of Corollary 101).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData IsLocalRing

namespace Hironaka

variable {k : Type u} [Field k]

namespace BOData

variable [CharZero k]

/-- Clause (1) of [Kol07, Theorem 103] read pointwise: the final birational transform has order
`< m` at every point, an order being at most the maximal order. -/
theorem ord_weakTransformSeq_lt {n m : ℕ} (B : BOData n m) (T : Triple k)
    (hT : Triple.BOClass n m T) (x : ((B.functor k).seq T hT).stage (Fin.last _)) :
    (((B.functor k).seq T hT).weakTransformSeq T.I (Fin.last _)).ord x < (m : ℕ∞) :=
  lt_of_le_of_lt (Scheme.IdealSheafData.le_maxOrd _ x) (B.maxOrd_lt k T hT)

/-- Clause (1) of [Kol07, Theorem 103] as the emptiness of the cosupport: no point of the final
stage has order `≥ m`, `cosupp(I_r, m) = ∅`. -/
theorem cosupp_eq_empty {n m : ℕ} (B : BOData n m) (T : Triple k) (hT : Triple.BOClass n m T) :
    {x : ((B.functor k).seq T hT).stage (Fin.last _) |
      (m : ℕ∞) ≤ (((B.functor k).seq T hT).weakTransformSeq T.I (Fin.last _)).ord x} = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
    absurd (B.ord_weakTransformSeq_lt T hT x) (not_lt.mpr hx)

end BOData

end Hironaka

namespace Hironaka.BO

open Hironaka Scheme BlowUpSequence

variable {k : Type u} [Field k]

/-- The domain of `BO_{n,m}` unfolded: `1 ≤ m`, `dim X ≤ n` and `max-ord I ≤ m`. -/
theorem boClass_iff (n m : ℕ) (T : Triple k) :
    Triple.BOClass n m T ↔ 1 ≤ m ∧ T.HasDimLE n ∧ T.I.maxOrd ≤ (m : ℕ∞) :=
  Iff.rfl

/-- The tuned triple has the same underlying scheme. -/
theorem tuned_X (T : Triple k) (m : ℕ) (hm : 1 ≤ m) : (T.tuned m hm).X.left = T.X.left := rfl

/-- The ideal of the tuned triple is the maximal coefficient ideal `W_{s(m)}(I)`. -/
theorem tuned_I (T : Triple k) (m : ℕ) (hm : 1 ≤ m) :
    (T.tuned m hm).I = IdealSheafData.W (T.X.left ↘ Spec (.of k)) T.I m (tuningParam m) := rfl

/-- The tuned triple has the same boundary divisor. -/
theorem tuned_E (T : Triple k) (m : ℕ) (hm : 1 ≤ m) : (T.tuned m hm).E = T.E := rfl

/-- The tuned triple of a triple with `dim X ≤ n` has `dim X ≤ n`, the scheme being unchanged. -/
theorem hasDimLE_tuned {T : Triple k} {n : ℕ} (h : T.HasDimLE n) (m : ℕ) (hm : 1 ≤ m) :
    (T.tuned m hm).HasDimLE n := h

/-- For `max-ord I = m ≥ 1` the tuned ideal has maximal order `s(m)` ([Kol07, Theorem 54.2 (i)]
for the exponent `m!`; `maxOrd_W` for an arbitrary exponent). -/
theorem maxOrd_tuned [CharZero k] {T : Triple k} {m : ℕ} (hI : T.I.maxOrd = m) (hm : 1 ≤ m) :
    (T.tuned m hm).I.maxOrd = (tuningParam m : ℕ∞) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact IdealSheafData.maxOrd_W (T.X.left ↘ Spec (.of k)) n T.I m hI hm _

/-- For `max-ord I = m ≥ 1` the tuned ideal is D-balanced with respect to `s(m)`
([Kol07, Corollary 101]). -/
theorem isDBalanced_tuned [CharZero k] {T : Triple k} {m : ℕ} (hI : T.I.maxOrd = m)
    (hm : 1 ≤ m) : IdealSheafData.IsDBalanced (T.X.left ↘ Spec (.of k)) (T.tuned m hm).I
        (tuningParam m) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact IdealSheafData.isDBalanced_W_tuningParam (T.X.left ↘ Spec (.of k)) n T.I m hI hm

/-- For `max-ord I = m ≥ 1` the tuned ideal is MC-invariant with respect to `s(m)`
([Kol07, Corollary 101]). -/
theorem isMCInvariant_tuned [CharZero k] {T : Triple k} {m : ℕ} (hI : T.I.maxOrd = m)
    (hm : 1 ≤ m) : IdealSheafData.IsMCInvariant (T.X.left ↘ Spec (.of k)) (T.tuned m hm).I
        (tuningParam m) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact IdealSheafData.isMCInvariant_W_tuningParam (T.X.left ↘ Spec (.of k)) n T.I m hI hm

/-- For `max-ord I = m ≥ 1`, a smooth blow-up sequence is of order `m` for `T` iff it is of order
`s(m)` for the tuned triple ([Kol07, Corollary 101]). -/
theorem isOrderSeq_tuned_iff [CharZero k] {T : Triple k} (S : BlowUpSequence T.X.left) {m : ℕ}
    (hI : T.I.maxOrd = m) (hm : 1 ≤ m) :
    S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ↔
      S.IsOrderSeq (T.X.left ↘ Spec (.of k)) (T.tuned m hm).I (T.tuned m hm).E (tuningParam m) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact Hironaka.BD.isOrderSeq_iff_tuned (T.X.left ↘ Spec (.of k)) n S T.I T.E m hI hm

/-- For a natural number `s ≥ 1`, the maximal order of an ideal sheaf is `< s` iff its order at
every point is `< s`: both say that every order is `≤ s − 1`, and `ℕ∞` has no limit point below a
natural number. Not in the sources. -/
theorem maxOrd_lt_iff_forall_ord_lt {X : Scheme.{u}} (J : X.IdealSheafData) {s : ℕ}
    (hs : 1 ≤ s) : J.maxOrd < (s : ℕ∞) ↔ ∀ x, J.ord x < (s : ℕ∞) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hs
  simp only [Nat.cast_succ, ENat.lt_add_one_iff (ENat.natCast_ne_top t)]
  exact IdealSheafData.maxOrd_le_iff J

/-- Along a smooth blow-up sequence of order `m` for `(X, I, E)` with `max-ord I = m ≥ 1`, the
final birational transform of the tuned ideal has maximal order `< s(m)` iff that of `I` has
maximal order `< m`. Not in the sources; it carries clause (1) of [Kol07, Theorem 103] from the
tuned triple back to `(X, I, E)`. The pointwise statement is
`Hironaka.BD.le_ord_weakTransformSeq_iff_tuned` at the last stage; the two suprema are compared
through `maxOrd_lt_iff_forall_ord_lt`. -/
theorem maxOrd_weakTransformSeq_lt_iff_tuned {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CharZero k]
    (n : ℕ) [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (I : X.IdealSheafData)
    (E : DivisorFamily X) (m : ℕ) (hI : I.maxOrd = m) (hm : 1 ≤ m) (h : S.IsOrderSeq f I E m) :
    (S.weakTransformSeq (IdealSheafData.W f I m (tuningParam m)) (Fin.last _)).maxOrd <
        (tuningParam m : ℕ∞) ↔
      (S.weakTransformSeq I (Fin.last _)).maxOrd < (m : ℕ∞) := by
  rw [maxOrd_lt_iff_forall_ord_lt _ (one_le_tuningParam m), maxOrd_lt_iff_forall_ord_lt _ hm]
  exact forall_congr' fun x => lt_iff_lt_of_le_iff_le
    (Hironaka.BD.le_ord_weakTransformSeq_iff_tuned f n S I E m hI hm h (Fin.last _) x).symm

/-- The tuned triple of a pull-back along a smooth morphism is the pull-back of the tuned triple:
the maximal coefficient ideal commutes with smooth pull-back (`W_comap_of_smooth`), as the
derivatives do. Used for [Kol07, 34.1]. -/
theorem isPullbackOf_tuned {T T' : Triple k} {g : T'.X.left ⟶ T.X.left} [Smooth g]
    (h : T'.IsPullbackOf T g) (m : ℕ) (hm : 1 ≤ m) :
    (T'.tuned m hm).IsPullbackOf (T.tuned m hm) g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  change IdealSheafData.W (T'.X.left ↘ Spec (.of k)) T'.I m (tuningParam m) =
    (IdealSheafData.W (T.X.left ↘ Spec (.of k)) T.I m (tuningParam m)).comap g
  rw [← IdealSheafData.W_comap_of_smooth (T.X.left ↘ Spec (.of k)) g T.I m (tuningParam m), h1, h2]

/-- The tuned triple of a change of fields is the change of fields of the tuned triple: the
maximal coefficient ideal commutes with base change along a field extension
(`W_comap_of_isPullback_specMap`). Used for [Kol07, 34.2]. -/
theorem isBaseChangeOf_tuned [CharZero k] {L : Type u} [Field L] {T : Triple k} {T' : Triple L}
    {σ : k →+* L} {p : T'.X.left ⟶ T.X.left} (h : T'.IsBaseChangeOf T σ p) (m : ℕ) (hm : 1 ≤ m) :
    (T'.tuned m hm).IsBaseChangeOf (T.tuned m hm) σ p := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  change IdealSheafData.W (T'.X.left ↘ Spec (.of L)) T'.I m (tuningParam m) =
    (IdealSheafData.W (T.X.left ↘ Spec (.of k)) T.I m (tuningParam m)).comap p
  rw [← IdealSheafData.W_comap_of_isPullback_specMap (T.X.left ↘ Spec (.of k)) h1 T.I m
      (tuningParam m), h2]

/-- The order condition of [Kol07, Definition 66] across a change of ideal: the smoothness and
normal-crossings clauses depend only on the centres, so the conditions for `(I, m)` and `(J, m')`
are equivalent once the order clauses are, stage by stage. This is the remark on the role of `E` in
the proof of [Kol07, Corollary 101]: adding `E` "poses the same restriction" on both. -/
theorem isOrderSeq_iff_of_ordAlongEq_iff {X : Scheme.{u}} (S : BlowUpSequence X)
    (f : X ⟶ Spec (.of k)) (I J : X.IdealSheafData) (E : DivisorFamily X) (m m' : ℕ)
    (h : ∀ i : Fin S.length,
      (S.weakTransformSeq I i.castSucc).OrdAlongEq (S.center i).support (m : ℕ∞) ↔
        (S.weakTransformSeq J i.castSucc).OrdAlongEq (S.center i).support (m' : ℕ∞)) :
    S.IsOrderSeq f I E m ↔ S.IsOrderSeq f J E m' :=
  and_congr Iff.rfl (forall_congr' fun i => and_congr Iff.rfl (h i))

end Hironaka.BO
