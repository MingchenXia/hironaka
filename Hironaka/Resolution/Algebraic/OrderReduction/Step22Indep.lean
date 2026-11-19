/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeq
public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
import Hironaka.Resolution.Algebraic.BoundaryClearing.ClassEtalePullback
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivAffine
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeqFunctor
import Hironaka.Resolution.Algebraic.OrderReduction.Step21MaximalContact
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.3 of order reduction: independence of the hypersurface of maximal contact

Step 2.3 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.3]) addresses the choice made
in Step 2.2: the hypersurface of maximal contact `H` is not unique, and for two of them, `H` and
`H'`, with `H + E` and `H' + E` having simple normal crossings, either boundary-clearing sequence
`BD_{n,m,0}(X, I, H + E)`, `BD_{n,m,0}(X, I, H' + E)` could serve to construct `BO_{n,m}(X, I, E)`.
Kollár's argument uses that `I` is MC-invariant: by [Kol07, Theorem 92] the triples `(X, I, H + E)`
and `(X, I, H' + E)` are then étale equivalent, hence so are the two blow-up sequences, and by
[Kol07, Theorem 97] étale equivalent blow-up sequences are identical.

Here the two Step 2.2 sequences are the boundary-clearing functor of [Kol07, Lemma 102]
(`bd (s m) j`, at the position `j` of the hypersurface, last in the boundary) applied to the tuned
Step 2.2 triples `(step22Triple T … H).tuned m hm` and `(step22Triple T … H').tuned m hm`: the same
`X_r`, the same tuned ideal `W_{s(m)}(I_r)`, MC-invariant by `isMCInvariant_tuned`, the same
exceptional sub-family `F_r`, and the transforms `H_r`, `H'_r` of the two hypersurfaces, both of
maximal contact for the tuned ideal at the mark `s(m)` (`isMaximalContact_step21_H` re-tuned by
`retune_keeps_maxContact`); both boundaries `F_r + H_r`, `F_r + H'_r` have normal crossings
everywhere (the field of `step22Triple`). Kollár's argument is then
`functor_independent_of_maximalContact_of_closed` of
`Hironaka/Resolution/Algebraic/MaximalContact/FunctorIndependence.lean` ([Kol07, Theorem 92] with an
affine étale cover, the étale equivalence of the two functor outputs, [Kol07, Theorem 97]), applied
to `(bd (s m) j).functor k` on the boundary-clearing class `BDClass n (s m) j`, which is closed
under étale pull-backs covering the cosupport (`bdClass_closedUnderEtalePullbackOverCosupp`):

* `step22_etaleEquivSeq_of_two_H`: at the mark, the two boundary-clearing sequences are étale
  equivalent in the sense of [Kol07, Definition 96], the first half of that argument;
* `step22_indep`: Step 2.2 does not depend on the choice of `H`; at the mark by the argument above
  (the second Step 2.2 triple is the first with its last member replaced, a definitional
  identification up to structure eta), below the mark both sides are empty;
* `step2Seq_indep`, `maxContactCase_indep`: Step 2 and `BO^H_{n,m}` likewise, through the
  unfoldings `step2Seq_eq`, `maxContactCase_of_maxOrd_eq` and `maxContactCase_of_maxOrd_lt`.

Kollár's separate hypothesis "`H + E` and `H' + E` have simple normal crossings" is not needed:
Step 2.1 supplies a boundary with normal crossings for every smooth hypersurface of maximal
contact (`Hironaka/Resolution/Algebraic/OrderReduction/Step21MaximalContact.lean`). The independence
makes `BO_{n,m}` well defined on the triples admitting a hypersurface of maximal contact, which Step
3 globalises (`Hironaka/Resolution/Algebraic/OrderReduction/Step3Globalization.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.BO

section Indep

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)
  {H H' : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
      (hH' : IsSmoothDivisor H')
  (hle' : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H')

/-- At the mark, the two boundary-clearing sequences of Step 2.2 for `H` and `H'` are étale
equivalent in the sense of [Kol07, Definition 96] ([Kol07, 104, Step 2.3]: the triples
`(X, I, H + E)` and `(X, I, H' + E)` are étale equivalent by [Kol07, Theorem 92], hence so are their
blow-up sequences): [Kol07, Theorem 92] on the tuned input with an affine étale cover
(`exists_etaleEquiv_isAffine`), through `etaleEquivSeq_of_functor` and the closure of the
boundary-clearing class under étale pull-backs covering the cosupport. -/
theorem step22_etaleEquivSeq_of_two_H
    (h : (step22Triple T hn hmax bd hm hH hle).I.maxOrd = m) :
    Nonempty (Scheme.IdealSheafData.EtaleEquivSeq ((step22Triple T hn hmax bd hm hH hle).X.left ↘
        Spec (.of k))
      ((step22Triple T hn hmax bd hm hH hle).tuned m hm).I (tuningParam m)
      (((bd (tuningParam m) _).functor k).seq
        ((step22Triple T hn hmax bd hm hH hle).tuned m hm)
        (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH hle) h hm))
      (((bd (tuningParam m) _).functor k).seq
        ((step22Triple T hn hmax bd hm hH' hle').tuned m hm)
        (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH' hle') h hm))) := by
  classical
  -- the two hypersurfaces `H_r`, `H'_r` are of maximal contact for the tuned ideal at the mark
  have hHr := retune_keeps_maxContact h hm
    (isMaximalContact_step21_H T hn hmax (bd m) hm hH hle (Fintype.card T.E.ι))
  have hH'r := retune_keeps_maxContact h hm
    (isMaximalContact_step21_H T hn hmax (bd m) hm hH' hle' (Fintype.card T.E.ι))
  have hI : Scheme.IdealSheafData.IsMCInvariant ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec
      (.of k))
      ((step22Triple T hn hmax bd hm hH hle).tuned m hm).I (tuningParam m) :=
    isMCInvariant_tuned h hm
  have hsnc' := (step22Triple T hn hmax bd hm hH' hle').isSnc
  obtain ⟨n', hn'⟩ := (step22Triple T hn hmax bd hm hH hle).smoothOfRelativeDimension
  -- Theorem 92 with an affine `U`
  obtain ⟨Q, hQ⟩ := Scheme.IdealSheafData.exists_etaleEquiv_isAffine
    ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k)) n'
    ((step22Triple T hn hmax bd hm hH hle).tuned m hm).I (one_le_tuningParam m) hI
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E)
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _))
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H' (Fin.last _))
    hHr hH'r (step22Triple T hn hmax bd hm hH hle).isSnc hsnc'
  -- the binders of Kollár 34.1 on `U`
  let _ : Q.U.Over (Spec (.of k)) :=
    ⟨Q.ψ ≫ ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))⟩
  have : Q.ψ.IsOver (Spec (.of k)) := ⟨rfl⟩
  have := Q.isOver_ψ'
  have : LocallyOfFiniteType (Q.U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (Q.ψ ≫ ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))))
  have : QuasiCompact (Q.U ↘ Spec (.of k)) := inferInstance
  have : IsSeparated (Q.U ↘ Spec (.of k)) := inferInstance
  have hU : ∃ n : ℕ, SmoothOfRelativeDimension n (Q.U ↘ Spec (.of k)) := by
    refine ⟨n', ?_⟩
    have h0 : SmoothOfRelativeDimension (0 + n')
        (Q.ψ ≫ ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))) := inferInstance
    simpa using h0
  -- the pulled-back triples are in Lemma 102's class
  have hDU := bdClass_closedUnderEtalePullbackOverCosupp n (tuningParam m) _
    ((step22Triple T hn hmax bd hm hH hle).tuned m hm)
    (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH hle) h hm) hU Q.ψ Q.covers
  have hDU' := bdClass_closedUnderEtalePullbackOverCosupp n (tuningParam m) _
    { (step22Triple T hn hmax bd hm hH hle).tuned m hm with
      E := ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).append
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H' (Fin.last _))
      isSnc := hsnc' }
    (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH' hle') h hm) hU Q.ψ' Q.covers'
  exact Scheme.IdealSheafData.etaleEquivSeq_of_functor ((bd (tuningParam m) _).functor k)
    ((bd (tuningParam m) _).commutesWithSmooth k)
    ((step22Triple T hn hmax bd hm hH hle).tuned m hm)
    (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH hle) h hm)
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E)
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _))
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H' (Fin.last _))
    rfl hsnc' (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH' hle') h hm) Q hU hDU hDU'

/-- Step 2.2 does not depend on the choice of the hypersurface of maximal contact
([Kol07, 104, Step 2.3]: "by (97) … these blow-up sequences are identical"): at the mark by
`functor_independent_of_maximalContact_of_closed` on the tuned Step 2.2 triple (the second triple
is the first with its last member replaced), below the mark both sides are empty. -/
theorem step22_indep :
    step22 T hn hmax bd hm hH hle = step22 T hn hmax bd hm hH' hle' := by
  classical
  by_cases h : (step22Triple T hn hmax bd hm hH hle).I.maxOrd = m
  · rw [step22_of_maxOrd_eq T hn hmax bd hm hH hle h,
      step22_of_maxOrd_eq T hn hmax bd hm hH' hle' h]
    exact Scheme.IdealSheafData.functor_independent_of_maximalContact_of_closed ((bd
        (tuningParam m) _).functor k)
      ((bd (tuningParam m) _).commutesWithSmooth k)
      (bdClass_closedUnderEtalePullbackOverCosupp n (tuningParam m) _)
      ((step22Triple T hn hmax bd hm hH hle).tuned m hm)
      (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH hle) h hm)
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E)
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _))
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H' (Fin.last _))
      rfl (step22Triple T hn hmax bd hm hH' hle').isSnc
      (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH' hle') h hm) (one_le_tuningParam m)
      (isMCInvariant_tuned h hm)
      (retune_keeps_maxContact h hm
        (isMaximalContact_step21_H T hn hmax (bd m) hm hH hle (Fintype.card T.E.ι)))
      (retune_keeps_maxContact h hm
        (isMaximalContact_step21_H T hn hmax (bd m) hm hH' hle' (Fintype.card T.E.ι)))
  · have hlt : (step22Triple T hn hmax bd hm hH hle).I.maxOrd < m :=
      lt_of_le_of_ne (bdClass_step22Triple T hn hmax bd hm hH hle).2.1 h
    exact (step22_of_maxOrd_lt T hn hmax bd hm hH hle hlt).trans
      (step22_of_maxOrd_lt T hn hmax bd hm hH' hle' hlt).symm

/-- Step 2 does not depend on the choice of the hypersurface of maximal contact
(`step2Seq = S₁.concat step22`). -/
theorem step2Seq_indep :
    step2Seq T hn hmax bd hm hH hle = step2Seq T hn hmax bd hm hH' hle' :=
  congrArg (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.concat
    (step22_indep T hn hmax bd hm hH hle hH' hle')

end Indep

section IndepAssembly

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hT : Triple.BOClass n m T)
  {H H' : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
      (hH' : IsSmoothDivisor H')
  (hle' : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H')
      (bd : ∀ m j : ℕ, BDData.{u} n m j)

/-- `BO^H_{n,m}(X, I, E) = BO^{H'}_{n,m}(X, I, E)` for any two smooth hypersurfaces of maximal
contact ([Kol07, 104, Step 2.3]): `BO_{n,m}` is well defined on the triples admitting one. At the
mark, Step 2 on the tuned triple with the re-tuned hypersurfaces (`step2Seq_indep`); below the
mark both sides are empty. -/
theorem maxContactCase_indep :
    maxContactCase T hT hH hle bd = maxContactCase T hT hH' hle' bd := by
  by_cases h : T.I.maxOrd = m
  · rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h,
      maxContactCase_of_maxOrd_eq T hT hH' hle' bd h]
    exact step2Seq_indep (T.tuned m hT.1) _ _ bd _ hH _ hH' _
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.2 h
    exact (maxContactCase_of_maxOrd_lt T hT hH hle bd hlt).trans
      (maxContactCase_of_maxOrd_lt T hT hH' hle' bd hlt).symm

end IndepAssembly

end Hironaka.BO
