/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyTuned
public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentFunctor
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalFamilyErasure
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferent
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The data of Lemma 102 are nil at a unit member

Kollár's convention deletes the empty blow-ups ([Kol07, 32]); the proof of [Kol07, Lemma 102] blows
up `Z_{-1} ⊂ E^j`, the union of the components of `E^j` inside the cosupport, and then runs the
inductive hypothesis on `S := E^j`. When the distinguished member `E^j` is the unit ideal, the
empty divisor, `Z_{-1}` is the unit ideal (`E^j ⊆ Z_{-1}`, `component_le_Zminus1` of
`Center.lean`), its blow-up is the empty blow-up, deleted, and `S` is the empty scheme, on which
every centre is the unit ideal, so the inductive functor's value is `nil`
(`eq_nil_of_noEmptyCenters`) and its push-forward to `X` is `nil`. So `bdData`
(`AssemblyTuned.lean`) is **nil at a unit member** at every mark: at mark `0` through the deleted
`π_{-1}` of `bdDataZero`; at mark `m + 1` through `dataFunctor`, the empty sequence below the mark
and, at the mark, the deleted `rawSeq` of `Output.lean` on the tuned triple. A bookkeeping property
of the construction, not in the sources.

* `rawSeq_eraseEmpty_eq_nil_of_eq_top`: the output of `Output.lean` with its empty blow-ups deleted
  is `nil` when the distinguished member is the unit ideal;
* `bdData_nilAtUnitMember`: `BDFamily.NilAtUnitMember` for `bdData` at every mark.

Used by `Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentGlobal.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence IsLocalRing Hironaka.BO

namespace Hironaka.BD

variable {k : Type u} [Field k] [CharZero k]

/-- When the distinguished member `E^j` is the unit ideal, the output of `Output.lean` with its
empty blow-ups deleted is the empty sequence ([Kol07, 32]): `S = E^j` is the empty scheme, the
inductive functor's value on the restricted triple is `nil` (no empty centres on an empty scheme),
and the first blow-up `π_{-1}` is empty, hence deleted. -/
theorem rawSeq_eraseEmpty_eq_nil_of_eq_top (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) {n : ℕ}
    (hn : T.HasDimLE n) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
    (hj : T.E.component j = ⊤) :
    (rawSeq T m j hI hmax hn B hDom).eraseEmpty = BlowUpSequence.nil T.X.left := by
  have hS : IsEmpty (T.E.component j).subscheme := by
    rw [hj]
    infer_instance
  have : IsEmpty (restrictedTriple T m j hI hmax).X.left :=
    ⟨fun x => isEmptyElim ((centerS T m j).blowUpπ.base x)⟩
  have hnil : B.seq (restrictedTriple T m j hI hmax)
      (hDom _ (hasDimLE_restrictedTriple T m j hI hmax hn) rfl) =
        BlowUpSequence.nil (centerS T m j).blowUp :=
    BlowUpSequence.eq_nil_of_noEmptyCenters _ (B.noEmptyCenters _ _)
  have hc : centerS T m j = ⊤ := Scheme.IdealSheafData.ext_stalkIdeal fun x => isEmptyElim x
  change ((cons (T.E.component j).subscheme (centerS T m j)
    (B.seq (restrictedTriple T m j hI hmax) _)).pushforward _).eraseEmpty = _
  rw [hnil, pushforward_cons, pushforward_nil]
  exact eraseEmpty_cons_nil_eq_nil _ (by rw [hc, Scheme.IdealSheafData.map_top])

/-- **`bdData` is nil at a unit member at every mark** ([Kol07, 32]): at mark `0`, `Z_{-1}` of the
unit ideal is the unit ideal (`component_le_Zminus1`) and the empty blow-up `π_{-1}` is deleted; at
mark `m + 1`, below the mark the value is `nil` by the convention of [Kol07, Theorem 68], and at
the mark the output on the tuned triple reduces to `nil` (`rawSeq_eraseEmpty_eq_nil_of_eq_top`). -/
theorem bdData_nilAtUnitMember (n : ℕ)
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ) (m : ℕ) :
    BDFamily.NilAtUnitMember (fun j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) := by
  intro k _ _ j T hT hj
  have hj' : T.E.component (T.E.nthIdx ⟨j, hT.2.2⟩) = ⊤ := hj
  cases m with
  | zero =>
    change (zeroFunctor n j).seq T hT = BlowUpSequence.nil T.X.left
    rw [zeroFunctor_seq, hj]
    have hZ := component_le_Zminus1 T 0 (T.E.nthIdx ⟨j, hT.2.2⟩)
    rw [hj'] at hZ
    exact eraseEmpty_cons_nil_eq_nil _ (top_le_iff.mp hZ)
  | succ m =>
    change (dataFunctor n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom (m + 1) k)).seq T hT =
      BlowUpSequence.nil T.X.left
    by_cases h : T.I.maxOrd = ((m + 1 : ℕ) : ℕ∞)
    · rw [dataFunctor_seq_of_maxOrd_eq n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom (m + 1) k) T
        hT h, functor_seq]
      exact rawSeq_eraseEmpty_eq_nil_of_eq_top _ _ _ _ _ _ _ _ hj'
    · exact dataFunctor_seq_of_maxOrd_lt n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom (m + 1) k)
        T hT (lt_of_le_of_ne hT.2.1 h)

end Hironaka.BD
