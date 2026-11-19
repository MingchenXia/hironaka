/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 100, the direction `⟹`: along a blow-up sequence

The direction of [Kol07, Theorem 100] proved first in Kollár's text: for `J ⊂ W_{ms}(I)`, a smooth
blow-up sequence of order `≥ m` starting with `(X, I, m)` is a smooth blow-up sequence of order
`≥ ms` starting with `(X, J, ms)`.

* **Along the sequence** ("we prove by induction on `r`"): at every stage `i`,
  `(Π_i)_*^{-1}(W_s(I), s) ⊆ W_s(I_i)` — induction on the succession, the step being the one-blow-up
  inclusion `markedTransform_W_le` (`Hironaka.Resolution.Algebraic.Tuning.Transform`) followed by
  the monotonicity of the marked recursion in its starting ideal (`markedTransformSeq_mono`),
  exactly as [Kol07, Theorem 76] is lifted along the sequence (`markedTransformSeq_W_le`); for `J ⊆
  W_s(I)`, `J_i ⊆ W_s(I_i)` by monotonicity (`markedTransformSeq_le_W`, Kollár's `J_{r−1} ⊆
  W_{ms}(I_{r−1})`).
* **The order estimate** (Kollár: "`ord_Z D^j(I_{r−1}) ≥ m − j`" when `ord_Z I_{r−1} ≥ m`, so the
  product `∏_j D^j(I_{r−1}, m)^{c_j}` has order `≥ ∑ (m − j) c_j ≥ ms` along `Z`): at a point `η`
  with `ord_η I ≥ m`, every generating product `∏_j (D^j I)^{e_j}` of `W_s(I)` has order
  `≥ ∑_j (m − j) e_j = wt(e) ≥ s` — [Kol07, Lemma 74 (3)] at the stalk
  (`le_ord_iff_le_ord_derivativeIter`), the order of a power is at least the multiple
  (`le_ord_pow`), the order of a product at least the sum (`le_ord_mul`, iterated:
  `sum_ord_le_ord_prod`) — and an ideal all of whose generators have order `≥ s` lies in `𝔪^s`
  (`le_ord_iff`), so `ord_η W_s(I) ≥ s` (`le_ord_W_of_le_ord`); hence `ord_Z I ≥ m` gives
  `ord_Z W_s(I) ≥ s` at every generic point of the closed set `Z` (`leOrdAlong_W`). The computation
  is at the stalk of `η` with no coordinates: the generic points of a centre are not closed, and the
  coordinate bridge `stalkIdeal_W` needs spanning coordinates, which exist at closed points only.
* **The direction assembled**: the smoothness and normal-crossing clauses of [Kol07, Definition 66]
  do not mention the ideal; at every stage `J_i ⊆ W_{ms}(I_i)`, `ord_{Z_i} I_i ≥ m` gives
  `ord_{Z_i} W_{ms}(I_i) ≥ ms` and so `ord_{Z_i} J_i ≥ ms` (the order is antitone in the ideal,
  [Kol07, Definition 59, (1)]) (`tuning_mp`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData IsLocalRing

namespace Hironaka.Local

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The order of a finite product of ideals is at least the sum of the orders (`le_ord_mul`
iterated; the empty product is the unit ideal, of order `0`). -/
theorem sum_ord_le_ord_prod {ι : Type*} (s : Finset ι) (g : ι → Ideal R) :
    ∑ i ∈ s, IsLocalRing.ord (g i) ≤ IsLocalRing.ord (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, Ideal.one_eq_top, IsLocalRing.ord_top]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    calc IsLocalRing.ord (g a) + ∑ i ∈ s, IsLocalRing.ord (g i) ≤ IsLocalRing.ord
           (g a) + IsLocalRing.ord (∏ i ∈ s, g i) := add_le_add le_rfl ih
      _ ≤ IsLocalRing.ord (g a * ∏ i ∈ s, g i) := le_ord_mul _ _

end Hironaka.Local

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-! ### The transform of the tuning ideal along the sequence -/

section Sequence

variable (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) (m s : ℕ)

include n

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, at every stage `i`,
`(Π_i)_*^{-1}(W_s(I), s) ⊆ W_s(I_i)` (the induction of the proof of [Kol07, Theorem 100]). Induction
on the succession: the first stage is the one-blow-up inclusion `markedTransform_W_le` (the centre
is smooth with `ord_Z I ≥ m`, by Definition 66), the marked recursion is monotone in its starting
ideal, and the tail is a sequence of order `≥ m` for the transformed data. -/
theorem markedTransformSeq_W_le (h : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    S.markedTransformSeq (W f I m s) s i ≤
      W (S.stageMap i ≫ f) (S.markedTransformSeq I m i) m s := by
  induction S with
  | nil Y =>
    change W f I m s ≤ W (𝟙 Y ≫ f) I m s
    rw [Category.id_comp]
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | i, hi⟩
    · change W f I m s ≤ W (𝟙 Y ≫ f) I m s
      rw [Category.id_comp]
    · change rest.markedTransformSeq ((W f I m s).markedTransform D s) s
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≤
        W ((rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f)
          (rest.markedTransformSeq (I.markedTransform D m) m ⟨i, Nat.lt_of_succ_lt_succ hi⟩) m s
      rw [Category.assoc]
      exact (markedTransformSeq_mono rest (markedTransform_W_le f n D I m s hm) s _).trans
        (ih (D.blowUpπ ≫ f) (I.markedTransform D m) (E.totalTransform D) ht
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-- The inductive statement as Kollár writes it in the proof of [Kol07, Theorem 100] ("since
`J ⊂ W_{ms}(I)`, we know that `J_{r−1} = (Π_{r−1})_*^{-1}(J, ms) ⊂ … = W_{ms}(I_{r−1})`"): for
`J ⊆ W_s(I)`, `J_i ⊆ W_s(I_i)` at every stage — `markedTransformSeq_W_le` with the monotonicity of
the marked recursion (`markedTransformSeq_mono`). -/
theorem markedTransformSeq_le_W (J : X.IdealSheafData) (hJW : J ≤ W f I m s)
    (h : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    S.markedTransformSeq J s i ≤ W (S.stageMap i ≫ f) (S.markedTransformSeq I m i) m s :=
  (markedTransformSeq_mono S hJW s i).trans (markedTransformSeq_W_le f n S I E m s h i)

end Sequence

/-! ### The order of the tuning ideal -/

section Order

variable (I : X.IdealSheafData) (m s : ℕ)

include n

/-- The order estimate of the proof of [Kol07, Theorem 100] at a point: if `ord_η I ≥ m` then
`ord_η W_s(I) ≥ s` — every generating product `∏_j (D^j I)^{e_j}` with `wt(e) ≥ s` has order
`≥ ∑_j (m − j) e_j = wt(e)`, since `ord_η D^j I ≥ m − j` ([Kol07, Lemma 74 (3)] at the stalk,
`j < m`; trivial for `j = m`), `ord (K^c) ≥ c · ord K` and `ord (K₁ K₂) ≥ ord K₁ + ord K₂`; and a
supremum of ideals of order `≥ s` has order `≥ s` (it lies in `𝔪^s`). No coordinates on the stalk
are used. -/
theorem le_ord_W_of_le_ord (η : X) (hη : (m : ℕ∞) ≤ I.ord η) :
    (s : ℕ∞) ≤ (W f I m s).ord η := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hj : ∀ j : Fin (m + 1),
      ((m - (j : ℕ) : ℕ) : ℕ∞) ≤ IsLocalRing.ord ((I.derivativeIter f j).stalkIdeal η) := by
    intro j
    rw [← ord_eq_ord_stalkIdeal]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp j.2) with hlt | heq
    · exact (le_ord_iff_le_ord_derivativeIter f n I η hlt).mp hη
    · rw [heq, Nat.sub_self, Nat.cast_zero]
      exact bot_le
  have hW : (W f I m s).stalkIdeal η =
      ⨆ x : {e : Fin (m + 1) → ℕ // s ≤ wt m e},
        (∏ j : Fin (m + 1), I.derivativeIter f j ^ x.1 j).stalkIdeal η := by
    have h1 : W f I m s = ⨆ x : {e : Fin (m + 1) → ℕ // s ≤ wt m e},
        ∏ j : Fin (m + 1), I.derivativeIter f j ^ x.1 j := by
      rw [W_eq]
      exact iSup_subtype'
    rw [h1]
    exact stalkIdeal_iSup _ η
  rw [ord_eq_ord_stalkIdeal, hW, IsLocalRing.le_ord_iff]
  refine iSup_le fun x => ?_
  rw [← IsLocalRing.le_ord_iff, stalkIdeal_finset_prod]
  calc (s : ℕ∞) ≤ (wt m x.1 : ℕ∞) := by exact_mod_cast x.2
    _ = ∑ j : Fin (m + 1), ((m - (j : ℕ) : ℕ) : ℕ∞) * (x.1 j : ℕ∞) := by
        unfold wt
        push_cast
        rfl
    _ ≤ ∑ j : Fin (m + 1), IsLocalRing.ord ((I.derivativeIter f j ^ x.1 j).stalkIdeal η) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [stalkIdeal_pow, mul_comm]
        exact (mul_le_mul_of_nonneg_left (hj j) bot_le).trans (le_ord_pow _ _)
    _ ≤ IsLocalRing.ord (∏ j : Fin (m + 1), (I.derivativeIter f j ^ x.1 j).stalkIdeal η) :=
        Local.sum_ord_le_ord_prod _ _

/-- The order estimate of the proof of [Kol07, Theorem 100] along a closed set ("if
`ord_Z I_{r−1} ≥ m`, then … `ord_Z ∏_j D^j(I_{r−1}, m)^{c_j} ≥ ∑ (m − j) c_j ≥ ms`"): for a closed
`Z`, `ord_Z I ≥ m` implies `ord_Z W_s(I) ≥ s`, at every generic point of `Z`. -/
theorem leOrdAlong_W (Z : Closeds X) (hm : I.LeOrdAlong Z (m : ℕ∞)) :
    (W f I m s).LeOrdAlong Z (s : ℕ∞) :=
  fun η hη => le_ord_W_of_le_ord f n I m s η (hm η hη)

end Order

/-! ### The direction assembled -/

section Assemble

variable (S : BlowUpSequence X) (I J : X.IdealSheafData) (E : DivisorFamily X) (m s : ℕ)

include n

/-- [Kol07, Theorem 100], the direction `⟹`: for `J ⊆ W_{ms}(I)`, a smooth blow-up sequence of order
`≥ m` starting with `(X, I, m, E)` is a smooth blow-up sequence of order `≥ ms` starting with
`(X, J, ms, E)`. The smoothness and normal-crossing clauses do not mention the ideal; at every stage
`J_i ⊆ W_{ms}(I_i)`, `ord_{Z_i} I_i ≥ m` gives `ord_{Z_i} W_{ms}(I_i) ≥ ms` and so
`ord_{Z_i} J_i ≥ ms` (the order is antitone in the ideal). -/
theorem tuning_mp (hJW : J ≤ W f I m (m * s)) (h : S.IsOrderGeSeq f I m E) :
    S.IsOrderGeSeq f J (m * s) E := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  have _ := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) h.1 i.castSucc
  have h1 := markedTransformSeq_le_W f n S I E m (m * s) J hJW h i.castSucc
  have h2 := leOrdAlong_W (S.stageMap i.castSucc ≫ f) n (S.markedTransformSeq I m i.castSucc) m
    (m * s) (S.center i).support (IsOrderGeSeq.leOrdAlong h i)
  exact fun η hη => (h2 η hη).trans (Scheme.IdealSheafData.ord_anti h1 η)

end Assemble

end Hironaka.Sequence
