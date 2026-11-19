/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.Kol07.IsoLocus
import Hironaka.Resolution.Algebraic.Kol07.IsoRestrict
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.OverSing
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The principalization sequence is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`

Clause (3) of [Kol07, Theorem 35] in a corrected form: the principalization `Π : X_r → X` of
`(X, I, E)` is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`, where `Sing E` is the locus where
two or more components of `E` meet. Kollár's text says "an isomorphism over `X ∖ cosupp I`", which
overlooks the disjoining blow-ups of [Kol07, 72], whose centers are the loci where several
components of `E` meet; the clause proved here adds `Sing E` to the excluded set. The proof reads
the definition `BP T = (disjoinSeq T.E ⧺ BMO_1(X', π^* I, 1, ∑ E^i))` with its empty blow-ups
deleted, and shows that every center of both halves avoids the preimage of
`U := X ∖ (cosupp I ∪ Sing E)`:

* the disjoining centers lie over `Sing E` (`support_center_disjoinSeq_le`; "the subset where `k`
  of the components intersect", [Kol07, 72]);
* the `BMO_1` centers lie in the cosupport of the marked ideal `(π^* I, 1)` at their stage
  (condition (4′) of [Kol07, Definition 66]), and over `U` the order of `π^* I` is `0`
  (`ord_eq_zero_iff`, `support_comap`): this is `center_disjoint_of_isOrderGeSeq_of_lt` at
  `m = 1`, from the field `isOrderGeSeq` of the functor;

so `isIso_composite_restrict_of_centers_disjoint` applies to both halves, the composite of the
concatenation is the composite of the two after the identification of the last stages
(`composite_concat`), restrictions of composites are composites of restrictions
(`morphismRestrict_comp`), and deleting the empty blow-ups does not change the isomorphism locus
(`isIso_eraseEmpty_composite_restrict`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence Hironaka.Stage

namespace Hironaka.Sequence

variable {k : Type u} [Field k] [CharZero k]

/-- Clause (3) of [Kol07, Theorem 35], with `Sing E` added to the excluded locus: `BP T` is an
isomorphism over `X ∖ (cosupp I ∪ Sing E)`. The disjoining centers lie over `Sing E`, the `BMO_1`
centers lie in the cosupport of `π^* I`. -/
theorem BP_isIso_restrict (T : Triple k) :
    IsIso ((BP T).composite ∣_ (T.I.support ⊔ T.E.singularLocus).compl) := by
  -- the disjoining half: its centers lie over `Sing E`
  have hS : IsIso ((disjoinSeq T.E).composite ∣_ (T.I.support ⊔ T.E.singularLocus).compl) := by
    refine isIso_composite_restrict_of_centers_disjoint (disjoinSeq T.E) _ fun i => ?_
    rw [Set.disjoint_left]
    intro x hx hxU
    have h1 : (disjoinSeq T.E).stageMap i.castSucc x ∈ (T.E.singularLocus : Set T.X.left) :=
      support_center_disjoinSeq_le T.E i hx
    have hxU' : (disjoinSeq T.E).stageMap i.castSucc x ∉
        ((T.I.support ⊔ T.E.singularLocus : Closeds T.X.left) : Set T.X.left) := hxU
    exact hxU' (by rw [Closeds.coe_sup]; exact Or.inr h1)
  -- the `BMO_1` half: its centers lie in the cosupport of `π^* I`
  have hR :
      IsIso (((BMO_m 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩).composite ∣_
      ((disjoinSeq T.E).composite ⁻¹ᵁ (T.I.support ⊔ T.E.singularLocus).compl)) := by
    obtain ⟨n, hn⟩ := (disjoinedTriple T).smoothOfRelativeDimension
    refine isIso_composite_restrict_of_centers_disjoint _ _
      (center_disjoint_of_isOrderGeSeq_of_lt
          ((disjoinedTriple T).X.left ↘ Spec (.of k)) n _
        ((BMO_m 1 k).isOrderGeSeq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)
        fun x hx => ?_)
    change (T.I.comap (disjoinSeq T.E).composite).ord x < ((1 : ℕ) : ℕ∞)
    have hx' : (disjoinSeq T.E).composite x ∉
        ((T.I.support ⊔ T.E.singularLocus : Closeds T.X.left) : Set T.X.left) := hx
    have hnot : x ∉ (T.I.comap (disjoinSeq T.E).composite).support := fun h =>
      hx' (by rw [Closeds.coe_sup]; exact Or.inl ((mem_support_comap_iff_apply _ _ _).mp h))
    rw [(Scheme.IdealSheafData.ord_eq_zero_iff _ _).mpr hnot]
    exact_mod_cast Nat.zero_lt_one
  -- the concatenation (`composite_concat`), then the deletion of the empty blow-ups; the two
  -- restricted factors are handed over by `exact` (their source objects agree only by unfolding
  -- `disjoinedTriple`, which instance search does not do)
  have hSR : IsIso (((disjoinSeq T.E).concat
      ((BMO_m 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)).composite ∣_
        (T.I.support ⊔ T.E.singularLocus).compl) := by
    have e := composite_concat (disjoinSeq T.E)
      ((BMO_m 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)
    rw [e]
    refine @isIso_restrict_comp _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @isIso_restrict_comp _ _ _ _ _ _ ?_ ?_
      · exact hR
      · exact hS
  exact @isIso_eraseEmpty_composite_restrict _ _ _ hSR

end Hironaka.Sequence
