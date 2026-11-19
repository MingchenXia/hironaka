/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.SncGlobalSubfamily
public import Hironaka.Resolution.Algebraic.OrderReduction.Step21Disjoint
public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
public import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.Tuning.MCTuned
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.2 of order reduction: restricting to the hypersurface of maximal contact

Step 2.2 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.2]) starts from the triple
`(X, I, E)` left by Step 2.1 together with a smooth hypersurface of maximal contact `H` such that
`H + E` has simple normal crossings; it replaces `I` by `W(I)` once more, keeps the birational
transforms of the old hypersurfaces of maximal contact rather than choosing new ones, declares `H`
the first member `E^0` of `H + E`, and applies the boundary-clearing functor of [Kol07, Lemma 102]
to `(X, I, H + E)` at that member. The resulting sequence `Π : X_r → X` has `cosupp Π⁻¹_*(I, m)`
disjoint from `Π⁻¹_* H`; since `H` is of maximal contact, the cosupport lies in `Π⁻¹_* H`, hence
"`cosupp Π⁻¹_*(I, m) = ∅`, as we wanted".

This module defines the objects of Step 2.2, of Step 2 and of the maximal-contact case of
`BO_{n,m}`; the theorems about them are in
`Hironaka/Resolution/Algebraic/OrderReduction/Step22Basic.lean`, `Step22Cosupp.lean`,
`Step22Indep.lean` and `Step22Assembly.lean`.

* **The Step 2.2 input triple** (`step22Triple`). With `S₁` the Step 2.1 sequence (`step21Seq`
  after all `card E.ι` rounds), `X_r := S₁.last`, `I_r := Π⁻¹_* I`, `E_r := Π⁻¹_tot E` and
  `H_r := Π⁻¹_* H`, this is the triple `(X_r, I_r, F_r + H_r)`, where `F_r` is the exceptional
  sub-family of `E_r` (`exceptionalFamily`: the members that are not birational transforms of
  original members) and `H_r` is appended last. Kollár's `(X, I, H + E)` with the full `E_r` is not
  used, because the birational transforms of the original members may fail to have normal
  crossings with `H_r` away from the cosupport, whereas `F_r + H_r` has normal crossings everywhere
  (`isSnc_exceptionalFamily_append`). The transforms of the original members are disjoint from
  `cosupp(I_r, m)` (`Hironaka/Resolution/Algebraic/OrderReduction/Step21Disjoint.lean`), hence from
  every later centre, so the two families agree wherever the normal-crossings clause of
  [Kol07, Definition 66] looks; the order condition for the original `(I_r, E_r)` is recovered in
  `Step22Basic.lean` (`isOrderSeq_step22_totalTransformSeq`). Kollár's "`E^0 := H` first, `j = 0`"
  becomes the position `card F_r.ι` of `H_r`.
* **The re-tuning of Step 2.2** (`step22Functor`). Kollár's "we can again replace `I` by `W(I)`" is
  made explicit: the boundary-clearing functor of [Kol07, Lemma 102] at the mark `m` on
  `BDClass n m j` is obtained from the one at the mark `s(m)` exactly as Step 1 obtains `BO_{n,m}`
  from the tuned functor (`OrderSeqAssignment.ofTunedClass`): `BD_{n,s(m),j}` applied to the tuned
  triple `(X, W_{s(m)}(I), E)` when `max-ord I = m`, the empty sequence below the mark
  (`bdClass_tuned` supplies the class obligation). The data `bd : ∀ m j, BDData n m j` are
  therefore Lemma 102 at every mark, which the induction on the dimension supplies.
* **Step 2.2** (`step22`): `step22Functor` at the position of `H_r`, applied to `step22Triple`,
  which lies in the boundary-clearing class (`bdClass_step22Triple`: `dim X_r ≤ n` along the stage
  map, `max-ord I_r ≤ m`, and the position).
* **Step 2** (`step2Seq`): Step 2.1 followed by Step 2.2 (`concat`).
* **The maximal-contact case of `BO_{n,m}`** (`maxContactCase`): on a triple of `BOClass n m` with
  a smooth hypersurface `H` of maximal contact for `(I, m)`, the Step 2 sequence of the tuned
  triple `(X, W_{s(m)}(I), E)` at the mark `s(m)` when `max-ord I = m`, and the empty sequence
  when `max-ord I < m`, the case split of `OrderSeqAssignment.ofTunedClass`. `H` stays of maximal
  contact for the tuned ideal because `MC(W_s(I)) = MC(I)` ([Kol07, Proposition 99 (4)];
  `retune_keeps_maxContact`, used again at Step 2.2 for `H_r`). Its dependence on `H` is only
  through Step 2.2. The sequence has no empty blow-up, so the deletion of empty blow-ups of
  [Kol07, 32] is the identity on it (`Step22Assembly.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.BO

section Retune

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- A smooth hypersurface of maximal contact for `(I, m)` is one for the tuned
`(W_{s(m)}(I), s(m))`: `MC(W_s(I)) = MC(I)` ([Kol07, Proposition 99 (4)];
`isMaximalContact_W_tuningParam`). The old hypersurface is kept after re-tuning, as
[Kol07, 104, Step 2.2] prescribes. -/
theorem retune_keeps_maxContact {T : Triple k} (hI : T.I.maxOrd = m) (hm : 1 ≤ m)
    {H : T.X.left.IdealSheafData}
    (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H) :
    IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k))
    (T.tuned m hm).I (tuningParam m) H := by
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  exact IdealSheafData.isMaximalContact_W_tuningParam (T.X.left ↘ Spec (.of k)) d T.I m hI hm hle

/-- A triple of the boundary-clearing class `BDClass n m j` with `max-ord I = m` tunes into
`BDClass n (s(m)) j` (`maxOrd_tuned`, `hasDimLE_tuned`). -/
theorem bdClass_tuned {T : Triple k} {j : ℕ} (hT : Triple.BDClass n m j T) (h : T.I.maxOrd = m)
    (hm : 1 ≤ m) : Triple.BDClass n (tuningParam m) j (T.tuned m hm) :=
  ⟨hasDimLE_tuned hT.1 m hm, le_of_eq (maxOrd_tuned h hm), hT.2.2⟩

/-- **The boundary-clearing functor of [Kol07, Lemma 102] at the mark `m` through the re-tuning**
("we can again replace `I` by `W(I)`", [Kol07, 104, Step 2.2]): `BD_{n,s(m),j}` on the tuned triple
when `max-ord I = m`, the empty sequence below the mark (`OrderSeqAssignment.ofTunedClass`, exactly
as Step 1 of Theorem 103). -/
noncomputable def step22Functor (bd : ∀ m j : ℕ, BDData.{u} n m j) (m j : ℕ) (hm : 1 ≤ m) :
    OrderSeqAssignment k m (Triple.BDClass n m j) :=
  OrderSeqAssignment.ofTunedClass ((bd (tuningParam m) j).functor k) (fun _ _ => hm)
    fun _ hT h => bdClass_tuned hT h hm

end Retune

section Step22

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j)

include hn in
/-- The triple induced at the last stage of a smooth blow-up sequence has `dim ≤ n`, the stage map
being smooth of the same relative dimension (the first clause of `bdClass_induced_last`). -/
theorem hasDimLE_induced_last {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) :
    (T.induced S hS (Fin.last _)).HasDimLE n := by
  obtain ⟨n', hn'n, hn'⟩ := hn
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  exact ⟨n', hn'n, IsSmooth.stageMap_smoothOfRelativeDimension hS.1 (Fin.last _)⟩

include hmax in
/-- The ideal induced at the last stage of a smooth blow-up sequence of order `m` without empty
blow-ups has `max-ord ≤ m`: by [Kol07, Definition 66] at the mark, and because the sequence is
empty below it (the second clause of `bdClass_induced_last`). -/
theorem maxOrd_induced_last_le {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) (hne : S.NoEmptyCenters) :
    (T.induced S hS (Fin.last _)).I.maxOrd ≤ (m : ℕ∞) := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  by_cases h : T.I.maxOrd = m
  · exact IsOrderSeq.maxOrd_weakTransformSeq_le (T.X.left ↘ Spec (.of k)) n' hS h (Fin.last _)
  · have hl : T.I.maxOrd < m := lt_of_le_of_ne hmax h
    have hnil := Hironaka.BO.eq_nil_of_isOrderSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k)) hS hne hl
    subst hnil
    exact hmax

section MaximalContact

variable (hm : 1 ≤ m) {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- **The Step 2.2 input triple** `(X_r, I_r, F_r + H_r)` ([Kol07, 104, Step 2.2]): the triple
induced at the end of Step 2.1, with its boundary replaced by the exceptional sub-family of `E_r`
followed by `H_r`, appended last (Kollár's "`E^0 := H` first" is the position `card F_r.ι`). Its
normal-crossings field is `isSnc_exceptionalFamily_append`: `F_r + H_r` has normal crossings
everywhere. -/
noncomputable def step22Triple : Triple k :=
  { T.induced (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1
      (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) (Fin.last _) with
    E := ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).append
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _))
    isSnc := by
      obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
      exact isSnc_exceptionalFamily_append n' (T.X.left ↘ Spec (.of k)) _
        (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) T.isSnc H hH
        (fun i => IsOrderSeq.isSmoothDivisor_strictTransformSeq (T.X.left ↘ Spec (.of k)) n' hm
          (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) hH hle i)
        (fun i => IsOrderSeq.strictTransformSeq_le_center_of_le_MC (T.X.left ↘ Spec (.of k)) n' hm
          (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) hH hle i) }

/-- The Step 2.2 input triple lies in the boundary-clearing class at the position of `H_r`
([Kol07, 104, Step 2.2]: "apply (102) to `(X, I, H + E)` with `j = 0`"). -/
theorem bdClass_step22Triple :
    Triple.BDClass n m
      (Fintype.card
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι)
      (step22Triple T hn hmax bd hm hH hle) :=
  ⟨hasDimLE_induced_last T hn (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)),
    maxOrd_induced_last_le T hmax (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
      (noEmptyCenters_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)),
    card_lt_card_ι_append _ _⟩

/-- **Step 2.2** ([Kol07, 104, Step 2.2]): the boundary-clearing functor at the position of `H_r`,
through the re-tuning (`step22Functor`), applied to the Step 2.2 input triple. -/
noncomputable def step22 : BlowUpSequence (step22Triple T hn hmax bd hm hH hle).X.left :=
  (step22Functor bd m _ hm).seq (step22Triple T hn hmax bd hm hH hle)
    (bdClass_step22Triple T hn hmax bd hm hH hle)

/-- **Step 2** of the proof of [Kol07, Theorem 103], on a triple with `max-ord I ≤ m` and a smooth
hypersurface of maximal contact `H`: Step 2.1 followed by Step 2.2 (`concat`). -/
noncomputable def step2Seq : BlowUpSequence T.X.left :=
  (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.concat (step22 T hn hmax bd hm hH hle)

end MaximalContact

end Step22

section Assembly

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- **`BO_{n,m}` in the maximal-contact case**, `BO^H_{n,m}(X, I, E)` (Steps 1–2 of the proof of
[Kol07, Theorem 103]): for a triple of `BOClass n m` with a smooth hypersurface `H` of maximal
contact for `(I, m)` and the boundary-clearing data at every mark, the Step 2 sequence of the tuned
triple `(X, W_{s(m)}(I), E)` at the mark `s(m)` when `max-ord I = m` (Step 1; `H` stays of maximal
contact by `retune_keeps_maxContact`), and the empty sequence when `max-ord I < m` (the remark
after [Kol07, Theorem 68]): the case split of `OrderSeqAssignment.ofTunedClass`. -/
noncomputable def maxContactCase (T : Triple k) (hT : Triple.BOClass n m T)
    {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
    (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
    (bd : ∀ m j : ℕ, BDData.{u} n m j) : BlowUpSequence T.X.left :=
  if h : T.I.maxOrd = m then
    step2Seq (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1) (le_of_eq (maxOrd_tuned h hT.1)) bd
      (one_le_tuningParam m) hH (retune_keeps_maxContact h hT.1 hle)
  else BlowUpSequence.nil T.X.left

end Assembly

end Hironaka.BO
