/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityPullback
public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Hironaka.Scheme.IdealSheaf.Order.Basic
public import Hironaka.Scheme.Snc.AppendEmpty
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Assembly of `BD_{n,m,j}`: the tuning layer, the mark `0`, and the data of clause (3)

[Kol07, Lemma 102] asserts, for every `m, j`, a smooth blow-up sequence functor `BD_{n,m,j}` of
order `m` on triples with `dim X ≤ n` and `max-ord I ≤ m`, with clauses (1)–(3). Its proof first
reduces to a D-balanced ideal (replace `I` by `W_{s(m)}(I)`, `Tuned.lean`), then builds the
sequence (`Center.lean` to `Output.lean`), proves its functoriality (`FunctorialityPullback.lean`,
`FunctorialityBaseChange.lean`), and ends with clause (3). This module defines the pieces of the
assembly and discharges the obligations they carry.

* `BD.zeroFunctor n j`, the functor at the mark `m = 0`. The class `BDClass n 0 j` is not empty
  (Kollár's `m` is a mark, `≥ 1`; `BDClass` does not exclude `0`): `max-ord I ≤ 0` makes `I` the
  unit ideal, every component of `E^j` lies in `cosupp(I, 0)`, so `Z_{-1} = E^j`, `π_{-1}` is the
  blow-up of `E^j` and the birational transform of `E^j` is empty. The functor is `π_{-1}` with its
  empty blow-up deleted ([Kol07, 32]); no inductive input is needed.
* `BD.tunedFunctor hm F hDom'`, the tuning device of Step 1 of the proof of [Kol07, Theorem 103]
  for Lemma 102's class: from a functor `F` of order `s(m)` on a class containing the tuned
  triples of `BDClass n m j`, the functor of order `m` on `BDClass n m j` whose value is
  `F(X, W_{s(m)}(I), E)` when `max-ord I = m` and the empty sequence when `max-ord I < m` (the
  convention of [Kol07, Theorem 68]: "the case `max-ord I < m` is trivial, that is, `X_r = X`").
  It is the instance at `C := BDClass n m j` of the class-generic `OrderSeqAssignment.ofTunedClass`
  (whose instance `OrderSeqAssignment.ofTuned` is the same device on the class of
  Theorem 103); the order condition is `isOrderSeq_iff_tuned`
  (`Tuned.lean`, [Kol07, Corollary 101] at this library's tuning parameter).
* `BD.domain_tuned`: the tuned triple of a triple of `BDClass n m j` above the mark lies in Lemma
  102's standing class `Domain n (s(m)) j` (`isDBalanced_tuned`, `maxOrd_tuned` of
  `Hironaka/Resolution/Algebraic/OrderReduction/Tuned.lean`).
* `BD.dataFunctor n m j hm B hDom`, **the functor `BD_{n,m,j}` over one field**, for `m ≥ 1`:
  `tunedFunctor` applied to `functor n (s(m)) j B hDom` of `Output.lean`, for a marked functor `B`
  of the shape of [Kol07, Theorem 69] at mark `s(m)` in dimensions `≤ n − 1` (the induction
  hypothesis `BMO_{≤ n−1, s(m)}`). Lemma 102's data `BDData n m j`, the functor over every field
  with clauses (1)–(2), is assembled from it in `AssemblyTuned.lean` (`bdData`) and from
  `zeroFunctor` in `AssemblyZero.lean` (`bdDataZero`).
* `BD.hypersurfaceTriple T hj J hJ`, the marked triple `(E^j, J, 1, (E − E^j)|_{E^j})` of clause
  (3), for `J` nonzero on every component of `E^j`. Its family is the members of `E − E^j`
  restricted to `E^j`, followed by an EMPTY member (the unit ideal): the exceptional member that the
  restricted marked triple of `Restriction.lean` carries at `Z_{-1} = ∅`, so that the latter is
  exactly its pull-back along the trivial blow-up; Kollár's `(E − E^j)|_{E^j}` has no such member
  (the total-transform convention of this library, as for `E_0` of `BD.piMinusOne`). The
  obligations: `E^j` is smooth of relative dimension one less (`isSmoothDivisor_component`), the
  family is snc (`isSnc_restrictedFamily` and `isSnc_append_top`).
* `BD.maxOrd_le_one_of_eq_map`, `BD.bdClass_one_of_eq_map`: the hypothesis of clause (3),
  `τ_*(O_{E^j}/J) = O_X/I`, i.e. `I = J.map τ`, puts `(X, I, E)` in the class of `BD_{n,1,j}`:
  "every local equation of `E^j` is an order 1 element in `I`" (the proof of [Kol07, Lemma 102]),
  so `max-ord I ≤ 1`.

Used by `AssemblyZero.lean`, and outside this directory by
`Hironaka/Resolution/Algebraic/OrderReduction/Step24ClosedEmbedding.lean`
(`Hironaka/Resolution/Algebraic/OrderReduction/Step21BoundaryClearing.lean` imports it and uses only
`BDData`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData Scheme
  BlowUpSequence IsLocalRing

namespace Hironaka.BD

variable {k : Type u} [Field k]

section Zero

variable [CharZero k]

/-- **`BD_{n,0,j}`**, the functor of [Kol07, Lemma 102] at the mark `0`: on `BDClass n 0 j` (where
`max-ord I ≤ 0` forces `I` to be the unit ideal), the trivial blow-up `π_{-1}` of `Z_{-1} = E^j`
with its empty blow-up deleted ([Kol07, 32]); a smooth blow-up sequence of order `0` starting with
`(X, I, E)` by `isOrderSeq_piMinusOne` (`Center.lean`). -/
noncomputable def zeroFunctor (n j : ℕ) : OrderSeqAssignment k 0 (Triple.BDClass n 0 j) where
  seq T hT := (piMinusOne T.I 0 (T.E.nth ⟨j, hT.2.2⟩)).eraseEmpty
  isOrderSeq T hT := by
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    have hmax : T.I.maxOrd = ((0 : ℕ) : ℕ∞) := le_antisymm hT.2.1 (by simp)
    exact IsOrderSeq.eraseEmpty (T.X.left ↘ Spec (.of k)) d
      (isOrderSeq_piMinusOne T 0 (pos T hT.2.2) hmax)
  noEmptyCenters _ _ := noEmptyCenters_eraseEmpty _

end Zero

section Tuned

variable [CharZero k] {n m j : ℕ} (hm : 1 ≤ m) {Dom' : Triple k → Prop}
  (F : OrderSeqAssignment k (tuningParam m) Dom')
  (hDom' : ∀ T : Triple k, Triple.BDClass n m j T → T.I.maxOrd = m → Dom' (T.tuned m hm))

/-- **The reduction to the tuned ideal on `BDClass n m j`** (the first paragraph of the proof of
[Kol07, Lemma 102]; the convention of [Kol07, Theorem 68] below the mark): from a smooth blow-up
sequence functor `F` of order `s(m)` on a class containing the tuned triples of `BDClass n m j`, the
functor of order `m` on `BDClass n m j` whose value on `(X, I, E)` is `F(X, W_{s(m)}(I), E)` when
`max-ord I = m` and the empty sequence when `max-ord I < m`. The instance of
`OrderSeqAssignment.ofTunedClass` at `C := BDClass n m j` (the mark bound is the global `hm`). -/
noncomputable def tunedFunctor : OrderSeqAssignment k m (Triple.BDClass n m j) :=
  OrderSeqAssignment.ofTunedClass F (fun _ _ => hm) hDom'

/-- The tuned triple of a triple of `BDClass n m j` with `max-ord I = m` lies in the standing class
`Domain n (s(m)) j` of `Restriction.lean` (the first paragraph of the proof of [Kol07, Lemma 102]):
`W_{s(m)}(I)` is D-balanced of maximal order `s(m)` (`isDBalanced_tuned`, `maxOrd_tuned`), the
dimension and the members of `E` are unchanged. -/
theorem domain_tuned {T : Triple k} (hT : Triple.BDClass n m j T) (h : T.I.maxOrd = m) :
    Domain n (tuningParam m) j (T.tuned m hm) :=
  ⟨Hironaka.BO.hasDimLE_tuned hT.1 m hm, Hironaka.BO.isDBalanced_tuned h hm,
    Hironaka.BO.maxOrd_tuned h hm, hT.2.2⟩

end Tuned

section Data

variable [CharZero k] (n m j : ℕ) (hm : 1 ≤ m) {Dom : MarkedTriple k → Prop}
  (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom T')

/-- **The functor `BD_{n,m,j}` over one field** ([Kol07, Lemma 102] with the first paragraph of its
proof), for a mark `m ≥ 1` and a marked functor `B` of the shape of [Kol07, Theorem 69] at mark
`s(m)` in dimensions `≤ n − 1` (the inductive hypothesis): the functor of `Output.lean` at order
`s(m)` on the tuned triple, and the empty sequence below the mark. Lemma 102's data `BDData n m j`
over every field is assembled from it in `AssemblyTuned.lean` (`bdData`). -/
noncomputable def dataFunctor : OrderSeqAssignment k m (Triple.BDClass n m j) :=
  tunedFunctor hm (functor n (tuningParam m) j B hDom) fun _ hT h => domain_tuned hm hT h

end Data

section Total

variable [CharZero k] (n : ℕ)

/-- **The functor `BD_{n,m,j}` over one field for every mark** ([Kol07, Lemma 102], "for every
`m, j`"), by a case split on the mark: `zeroFunctor` at `m = 0` and `dataFunctor` at `m ≥ 1`. The
inductive input `B`, a marked functor at mark `s(m)` in dimensions `≤ n − 1`, is an argument at
every mark so that the functor has one signature, Kollár's `BD_{n,m,j}` for every `m`; the
definition does not need it at `m = 0`, because there `I` is the unit ideal and the value is the
trivial blow-up `π_{-1}` alone, without any inductive input (`zeroFunctor`). -/
noncomputable def totalFunctor : (m j : ℕ) → {Dom : MarkedTriple k → Prop} →
    (B : OrderGeSeqAssignment k Dom) →
    (∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom T') →
    OrderSeqAssignment k m (Triple.BDClass n m j)
  | 0, j, _, _, _ => zeroFunctor n j
  | m + 1, j, _, B, hDom => dataFunctor n (m + 1) j (Nat.le_add_left 1 m) B hDom

end Total

section ClauseThree

variable [CharZero k] (T : Triple k) {j : ℕ} (hj : j < Fintype.card T.E.ι)
  (J : (T.E.nth ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroEverywhere J)

/-- **The marked triple `(E^j, J, 1, (E − E^j)|_{E^j})`** of clause (3) of [Kol07, Lemma 102], for
an ideal `J ⊂ O_{E^j}` nonzero on every irreducible component of `E^j`; its family is the members of
`E − E^j` restricted to `E^j`, followed by an empty member (see the module docstring). `E^j` is
smooth over `k` of relative dimension one less than `X` (`isSmoothDivisor_component`,
`Restriction.lean`), `J` is nonzero on every component by hypothesis, and the family is snc
(`isSnc_restrictedFamily`, `isSnc_append_top`). -/
noncomputable def hypersurfaceTriple : MarkedTriple k where
  X := .ofHom ((T.E.nth ⟨j, hj⟩).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
    (
      inferInstanceAs (FiniteType ((T.E.nth ⟨j, hj⟩).subschemeι ≫ (T.X.left ↘ Spec (.of k)))))
    (
      inferInstanceAs (IsSeparated ((T.E.nth ⟨j, hj⟩).subschemeι ≫ (T.X.left ↘ Spec (.of k)))))
  smoothOfRelativeDimension := by
    obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
    exact ⟨n' - 1, smoothOfRelativeDimension_of_isSmoothDivisor (T.X.left ↘ Spec (.of k)) n' _
      (isSmoothDivisor_component T (pos T hj))⟩
  I := J
  isNonzeroEverywhere := hJ
  E := ((T.E.erase (pos T hj)).comap (T.E.nth ⟨j, hj⟩).subschemeι).append ⊤
  isSnc := DivisorFamily.isSnc_append_top _ (isSnc_restrictedFamily T (pos T hj))
  m := 1

/-- The marked triple of clause (3) has dimension `≤ n − 1` when `(X, I, E)` has dimension `≤ n`
(Kollár's `BMO_{n−1,1}`, [Kol07, Lemma 102]). -/
theorem hasDimLE_hypersurfaceTriple {n : ℕ} (hn : T.HasDimLE n) :
    (hypersurfaceTriple T hj J hJ).toTriple.HasDimLE (n - 1) := by
  obtain ⟨n', hn'n, hn'⟩ := hn
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  exact ⟨n' - 1, by omega, smoothOfRelativeDimension_of_isSmoothDivisor
    (T.X.left ↘ Spec (.of k)) n' _
    (isSmoothDivisor_component T (pos T hj))⟩

variable (hIJ : T.I = J.map (T.E.nth ⟨j, hj⟩).subschemeι)

omit [CharZero k] in
include hIJ in
/-- If `O_X/I = τ_*(O_{E^j}/J)`, i.e. `I = J.map τ`, then `max-ord I ≤ 1` ("Every local equation of
`E^j` is an order 1 element in `I`", the proof of [Kol07, Lemma 102]): `I` contains the ideal of
`E^j` (`ker τ = ⊥.map τ ≤ J.map τ`), which has order `1` along `E^j` (a smooth divisor), and `I` is
the unit ideal off `E^j` (its support lies in the closed image of `τ`). -/
theorem maxOrd_le_one_of_eq_map : T.I.maxOrd ≤ ((1 : ℕ) : ℕ∞) := by
  rw [maxOrd_le_iff]
  intro x
  by_cases hx : x ∈ (T.E.nth ⟨j, hj⟩).support
  · have h1 : (T.E.nth ⟨j, hj⟩).subschemeι.ker ≤ J.map (T.E.nth ⟨j, hj⟩).subschemeι := by
      rw [← Scheme.IdealSheafData.map_bot]
      exact Scheme.IdealSheafData.map_mono _ bot_le
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hIJ] at h1
    calc T.I.ord x ≤ (T.E.nth ⟨j, hj⟩).ord x := Scheme.IdealSheafData.ord_anti h1 x
      _ = 1 := (isSmoothDivisor_component T (pos T hj)).ord_eq_one hx
  · have hxI : x ∉ T.I.support := by
      intro hxm
      rw [hIJ, Scheme.IdealSheafData.support_map] at hxm
      have hsub : closure ((T.E.nth ⟨j, hj⟩).subschemeι '' J.support) ⊆
          ((T.E.nth ⟨j, hj⟩).support : Set T.X.left) := by
        refine (closure_mono (Set.image_subset_range _ _)).trans ?_
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact (T.E.nth ⟨j, hj⟩).support.isClosed.closure_subset
      exact hx (hsub hxm)
    have : ¬ (1 : ℕ∞) ≤ T.I.ord x := fun h => hxI ((one_le_ord_iff _ _).mp h)
    exact (not_le.mp this).le

omit [CharZero k] in
include hIJ in
/-- Under the hypothesis of clause (3) of [Kol07, Lemma 102], `(X, I, E)` lies in the class of
`BD_{n,1,j}` when `dim X ≤ n`. -/
theorem bdClass_one_of_eq_map {n : ℕ} (hn : T.HasDimLE n) : Triple.BDClass n 1 j T :=
  ⟨hn, maxOrd_le_one_of_eq_map T hj J hIJ, hj⟩

end ClauseThree

end Hironaka.BD
