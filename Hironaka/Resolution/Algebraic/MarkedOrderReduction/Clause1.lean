/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Assembly
import Hironaka.Resolution.Algebraic.Kol07.IsoLocus
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.Monomial.Geometric.OrderSeq
import Hironaka.Scheme.BlowUpSequence.ConcatMarked
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (1) of marked order reduction: the final maximal order is below the mark

Clause (1) of [Kol07, Theorem 107]: at the end of `BMO_{n,m}(X, I, m, E)` the marked transform
`(I_r, m)` has `max-ord I_r < m`. After Steps 1 and 2 the induced marked triple has `max-ord N(I) <
m` and `cosupp(I, m) ∩ cosupp N(I) = ∅`; Kollár then runs Step 3 on `X ∖ cosupp N(I)`, where `I =
M(I)`, and at its end `max-ord < m` ([Kol07, 111, Steps 2–3]). Here the geometric Step 3 is run on
`X` for `(M(I), m, E)` (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean`), and
the result is read for `(I, m)` through two facts not in the sources as such:

* the propagation `center_step3Seq_disjoint`: every centre of Step 3 avoids the preimage of
  `cosupp N(I)`, since the centres lie in `cosupp(M_i, m)` and over `cosupp N(I)` the order of
  `M_i` is the order of `M(I)`, which is `≤ ord I < m` there
  (`Hironaka/Resolution/Algebraic/Kol07/IsoLocus.lean`);
* the assembly `maxOrd_markedTransformSeq_step3Seq_lt`: at a point of the end stage over
`cosupp N(I)` the marked transform of `(I, m)` is the pull-back (the blow-ups are isomorphisms
there), of order `ord I < m`; at a point off it, `I = M(I)` locally at the image, so the marked
transforms of `(I, m)` and `(M(I), m)` have the same stalk (`stalkIdeal_markedTransformSeq_congr`),
and `realize_maxOrd_lt` bounds the latter.

`maxOrd_lt` is clause (1) for `BMO.functor`: along the concatenation `Step 1 ++ Step 2 ++ Step 3`
the end data are the end data of Step 3 for the marked triple induced after Step 2
(`markedEnd_concat_iff`), whose separation order is `0` (`sepOrder_induced_step2_eq_zero`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Monomial Hironaka.Monomial.PieceFamily Hironaka.Sequence

namespace Hironaka.BMO

section MaxOrd

variable {X : Scheme.{u}}

/-- `max-ord I < m` (for `1 ≤ m`) once `ord_x I < m` at every point: the maximal order is the
supremum of the orders, and `ord_x I < m` means `ord_x I ≤ m − 1` in `ℕ∞`. -/
theorem maxOrd_lt_of_forall_lt {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ x, I.ord x < (m : ℕ∞)) : I.maxOrd < (m : ℕ∞) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  have hle : I.maxOrd ≤ (m' : ℕ∞) := (IdealSheafData.maxOrd_le_iff (I := I)).2 fun x =>
    (ENat.lt_add_one_iff (ENat.natCast_ne_top m')).1 (by exact_mod_cast h x)
  exact lt_of_le_of_lt hle (by exact_mod_cast Nat.lt_succ_self m')

end MaxOrd

section Step3

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k) {n m : ℕ}

/-- Step 3 is a smooth blow-up sequence of order `≥ m` for `(X, M(I), m, E)` (conditions
(2′)–(4′) of [Kol07, Definition 66] for `(M(I), m)`; `realize_isOrderGeSeq` through
`monomial_exponentAt_step3Family`), the form the propagation uses. -/
theorem step3Seq_isOrderGeSeq_monomialPart (hT : T.BMOClass n m) :
    (step3Seq T hT).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) (monomialPart T.I T.E) m T.E := by
  have := T.smooth
  have h := realize_isOrderGeSeq (f := T.X.left ↘ Spec (.of k)) (Φ := step3Family T) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1
  rwa [monomial_exponentAt_step3Family] at h

/-- The propagation: after Step 2 (`sepOrder T = 0`) every centre of Step 3 avoids the preimage of
`supp N(I)`. By induction along the run, the centres lie in `cosupp(M_i, m)`, and over the locus
where the blow-ups are isomorphisms `ord M_i = ord M(I) ≤ ord I < m` at points of `supp N(I)`
(`setOf_le_ord_subset_compl_support_of_sepOrder_eq_zero`). Not in the sources as such. -/
theorem center_step3Seq_disjoint (hT : T.BMOClass n m) (h0 : sepOrder T = 0)
    (i : Fin (step3Seq T hT).length) :
    Disjoint ((((step3Seq T hT).center i).support : Set ((step3Seq T hT).stage i.castSucc)))
      ((step3Seq T hT).stageMap i.castSucc ⁻¹' ((nonmonomialPart T.I T.E).support : Set
        T.X.left)) := by
  obtain ⟨n', -, hn'⟩ := hT.2.1
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  refine center_disjoint_of_isOrderGeSeq_of_lt (T.X.left ↘ Spec (.of k)) n' (step3Seq T hT)
    (step3Seq_isOrderGeSeq_monomialPart T hT) (fun x hx => ?_) i
  have h1 : T.I.ord x < (T.m : ℕ∞) := by
    by_contra hle
    exact setOf_le_ord_subset_compl_support_of_sepOrder_eq_zero T h0 (not_lt.1 hle) hx
  rw [hT.2.2] at h1
  have hle : T.I ≤ monomialPart T.I T.E :=
    calc T.I = monomialPart T.I T.E * nonmonomialPart T.I T.E :=
          (monomialPart_mul_nonmonomialPart T.toTriple).symm
      _ ≤ monomialPart T.I T.E := IdealSheafData.mul_le_self_left _ _
  exact lt_of_le_of_lt (IdealSheafData.ord_anti hle x) h1

/-- For a marked triple with `cosupp(I, m) ∩ supp N(I) = ∅`, the marked transform of `(I, m)` at the
end of Step 3 has `max-ord < m` (clause (1) of [Kol07, Theorem 107] for the Step 3 part): over
`supp N(I)` the order is the order at the image (`ord_markedTransformSeq_eq_of_disjoint` with
`center_step3Seq_disjoint`), `< m` there; off it `I = M(I)` locally and `step3Seq_maxOrd_lt` bounds
the order. -/
theorem maxOrd_markedTransformSeq_step3Seq_lt (hT : T.BMOClass n m) (h0 : sepOrder T = 0) :
    ((step3Seq T hT).markedTransformSeq T.I T.m (Fin.last (step3Seq T hT).length)).maxOrd <
      (m : ℕ∞) := by
  have hmT : T.m = m := hT.2.2
  refine maxOrd_lt_of_forall_lt hT.1 fun x => ?_
  by_cases hx : (step3Seq T hT).stageMap (Fin.last _) x ∈
      ((nonmonomialPart T.I T.E).support : Set T.X.left)
  · rw [ord_markedTransformSeq_eq_of_disjoint (step3Seq T hT) (center_step3Seq_disjoint T hT h0)
      _ x hx]
    by_contra hle
    have h' : (T.m : ℕ∞) ≤ T.I.ord ((step3Seq T hT).stageMap (Fin.last _) x) := by
      rw [hmT]
      exact not_lt.1 hle
    exact setOf_le_ord_subset_compl_support_of_sepOrder_eq_zero T h0 h' hx
  · have hst : T.I.stalkIdeal ((step3Seq T hT).stageMap (Fin.last _) x) =
        (monomialPart T.I T.E).stalkIdeal ((step3Seq T hT).stageMap (Fin.last _) x) :=
      stalkIdeal_eq_monomialPart_of_notMem_support T hx
    rw [IdealSheafData.ord_eq_ord_stalkIdeal, stalkIdeal_markedTransformSeq_congr
        (step3Seq T hT) T.m _ x hst,
      ← IdealSheafData.ord_eq_ord_stalkIdeal, hmT]
    exact lt_of_le_of_lt (IdealSheafData.le_maxOrd (I := _) x) (step3Seq_maxOrd_lt T hT)

end Step3

section Assembly

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}
  (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)

/-- **At the end of `BMO_{n,m}(X, I, m, E)` the marked transform of `(I, m)` has `max-ord < m`**
(clause (1) of [Kol07, Theorem 107]; the field `BMOData.maxOrd_lt` for `BMO.functor`): the end
data of `Step 1 ++ Step 2 ++ Step 3` are the end data of Step 3 for the marked triple induced
after Step 2 (`markedEnd_concat_iff`, twice), whose separation order is `0`
(`sepOrder_afterStep2_eq_zero`), where `maxOrd_markedTransformSeq_step3Seq_lt` applies. -/
theorem maxOrd_lt :
    (((functor bo m).seq T hT).markedTransformSeq T.I T.m
      (Fin.last ((functor bo m).seq T hT).length)).maxOrd < (m : ℕ∞) := by
  change ((bmoSeq bo T hT).markedTransformSeq T.I T.m (Fin.last (bmoSeq bo T hT).length)).maxOrd <
    (m : ℕ∞)
  unfold bmoSeq
  refine (markedEnd_concat_iff (fun {Y} (J : Y.IdealSheafData) (_ : DivisorFamily Y) =>
    J.maxOrd < (m : ℕ∞)) _ _ T.I T.m T.E).2 ?_
  refine (markedEnd_concat_iff (fun {Y} (J : Y.IdealSheafData) (_ : DivisorFamily Y) =>
    J.maxOrd < (m : ℕ∞)) _ _ (afterStep1 bo T hT).I (afterStep1 bo T hT).m
    (afterStep1 bo T hT).E).2 ?_
  exact maxOrd_markedTransformSeq_step3Seq_lt (afterStep2 bo T hT) (bmoClass_afterStep2 bo T hT)
    (sepOrder_afterStep2_eq_zero bo T hT)

end Assembly

end Hironaka.BMO
