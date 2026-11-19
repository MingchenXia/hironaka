/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The principalization sequence: unfolding, the empty blow-up convention, the empty boundary

The first facts about `Hironaka.Sequence.BP`
(`Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization.lean`): its unfolding (`BP_eq`); the
empty blow-up convention of [Kol07, 32], "the final outputs of the named blow-up sequence functors …
do not contain empty blow-ups", as a theorem (`BP_noEmptyCenters`, the definition deletes them); and
the case of an empty boundary (`BP_of_isEmpty`): for `E = ∅` the disjoining sequence is the empty
sequence (`disjoinSeq_of_isEmpty`), so `BP T` is `BMO_1(X, I, 1, ∅)` itself, up to two transports.
First, `disjoinSeq T.E = nil` holds only propositionally (`Fintype.card` of an empty index type is
not `0` by `rfl`), so the disjoined triple `(X', π^* I, ∑ E^i)` lives on a scheme `X'` merely equal
to `X`: `concat_pullback_eqToHom` moves the `BMO_1` part across the `eqToHom` isomorphism, and the
commutation of `BMO_1` with smooth surjections [Kol07, 34.1] at that isomorphism
(`dimFreeBMO_commutesWithSmooth`) identifies the value. Second, the collapsed family `∑ E^i` of an
empty `E` is not empty: it has the single member `E^0 = ∏_{i ∈ ∅} … = 𝒪_X`, the empty divisor
(`disjoinedFamily_component_bot`, `card_disjoinedFamily`), so the two boundaries differ by one unit
member, which the indifference of `BMO_1` to unit members (`dimFreeBMO_indifferentToEmptyMembers`)
removes along the unique order embedding out of the empty index type. Finally the output of `BMO_1`
has no empty center (`OrderGeSeqAssignment.noEmptyCenters`), so the `eraseEmpty` of the definition
is the identity there (`eraseEmpty_eq_self_iff`).

The empty-boundary case is what the closed embedding clause of [Kol07, Theorem 35 (5)] reduces
to, since that clause is stated for `E = ∅`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Hironaka BlowUpSequence Hironaka.Stage

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- The unfolding of the principalization sequence, by definition. -/
theorem BP_eq (T : Triple k) :
    BP T = ((disjoinSeq T.E).concat
      ((BMO_m 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)).eraseEmpty :=
  rfl

/-- `BP T` has no empty center: the definition deletes them, as the empty blow-up convention of
[Kol07, 32] requires. -/
theorem BP_noEmptyCenters (T : Triple k) : (BP T).NoEmptyCenters :=
  noEmptyCenters_eraseEmpty _

/-- A blow-up sequence that is (propositionally) the empty sequence has composite `𝟙` up to the
identification of its last stage with the base. -/
theorem eqToHom_comp_composite_of_eq_nil {X : Scheme.{u}} {S : BlowUpSequence X}
    (hS : S = nil X) (p : X = S.last) : eqToHom p ≫ S.composite = 𝟙 X := by
  subst hS
  exact (Category.comp_id (eqToHom p)).trans (eqToHom_refl X p)

/-- For `E = ∅` the principalization sequence is `BMO_1(X, I, 1, ∅)` itself: with `k = 0`
components there are no disjoining steps [Kol07, 72]. The proof moves the `BMO_1` part across the
`eqToHom` isomorphism `X ≅ X'` (`concat_pullback_eqToHom`, then the commutation of `BMO_1` with
smooth surjections [Kol07, 34.1] at the isomorphism) after removing the one unit member of the
collapsed family by the indifference of `BMO_1` to unit members; the final `eraseEmpty` is the
identity since the output of `BMO_1` has no empty center. -/
theorem BP_of_isEmpty (T : Triple k) (hE : IsEmpty T.E.ι) :
    BP T = (BMO_m 1 k).seq ⟨T, 1⟩ ⟨le_rfl, rfl⟩ := by
  classical
  have hS : disjoinSeq T.E = nil T.X.left := disjoinSeq_of_isEmpty T.E hE
  have e0 : T.X.left = (disjoinSeq T.E).last := congrArg BlowUpSequence.last hS.symm
  change ((disjoinSeq T.E).concat
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩
          ⟨le_rfl, rfl⟩)).eraseEmpty =
    (dimFreeBMO stage0 1 k).seq ⟨T, 1⟩ ⟨le_rfl, rfl⟩
  set R : BlowUpSequence (disjoinSeq T.E).last :=
    (dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩
  -- Step A: the concatenation with a (propositionally) empty first sequence is the transported
  -- second sequence
  rw [← concat_pullback_eqToHom hS.symm R, concat_nil]
  change (R.pullback (eqToHom e0)).eraseEmpty = _
  -- Step B: remove the one unit member `E^0 = 𝒪` of the collapsed family of the empty `E`
  set E₀ : DivisorFamily (disjoinSeq T.E).last := T.E.comap (inv (eqToHom e0)) with hE₀def
  have hE₀ι : IsEmpty E₀.ι := hE
  have hE₀ : E₀.IsSnc :=
    isSnc_of_isEmpty ((disjoinedTriple T).X.left ↘ Spec (.of k)) E₀ hE₀ι
  set MD' : MarkedTriple k :=
    { (⟨disjoinedTriple T, 1⟩ : MarkedTriple k) with E := E₀, isSnc := hE₀ }
  have hbot : ∀ b : (collapsedFamily (disjoinSeq T.E) T.E).ι,
      (collapsedFamily (disjoinSeq T.E) T.E).component b = ⊤ := by
    intro b
    have hcard : Fintype.card (collapsedFamily (disjoinSeq T.E) T.E).ι = 1 := by
      rw [card_disjoinedFamily, length_disjoinSeq, Fintype.card_eq_zero]
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
    have hb : b = (⊥ : WithBot {a : ((disjoinSeq T.E).totalTransformSeq T.E (Fin.last _)).ι //
        ¬ a ∈ Set.range ((disjoinSeq T.E).originalIdx T.E (Fin.last _))}) :=
      (hx b).trans (hx _).symm
    rw [hb, disjoinedFamily_component_bot, Fintype.prod_empty]
    exact Scheme.IdealSheafData.one_eq_top
  have hB : R = (dimFreeBMO stage0 1 k).seq MD' ⟨le_rfl, rfl⟩ :=
    dimFreeBMO_indifferentToEmptyMembers stage0 1 ⟨disjoinedTriple T, 1⟩ E₀ hE₀
      OrderEmbedding.ofIsEmpty (fun i => hE₀ι.elim i) (fun b _ => hbot b) ⟨le_rfl, rfl⟩
      ⟨le_rfl, rfl⟩
  -- Step C: the commutation with smooth surjections, [Kol07, 34.1], at the isomorphism `eqToHom e0`
  have hsm : Smooth (eqToHom e0) := Hironaka.BD.smooth_eqToHom e0
  have hsurj : Function.Surjective (eqToHom e0) := surjective_of_isIso (eqToHom e0)
  have hover : eqToHom e0 ≫ ((disjoinSeq T.E).composite ≫ (T.X.left ↘ Spec (.of k))) =
      (T.X.left ↘ Spec (.of k)) := by
    rw [← Category.assoc, eqToHom_comp_composite_of_eq_nil hS, Category.id_comp]
  have hI : T.I = (T.I.comap (disjoinSeq T.E).composite).comap (eqToHom e0) := by
    rw [← Scheme.IdealSheafData.comap_comp, eqToHom_comp_composite_of_eq_nil hS,
      Scheme.IdealSheafData.comap_id]
  have hEq : T.E = E₀.comap (eqToHom e0) := by
    rw [hE₀def, ← DivisorFamily.comap_comp, IsIso.hom_inv_id, DivisorFamily.comap_id]
  have hpb : (⟨T, 1⟩ : MarkedTriple k).IsPullbackOf MD' (eqToHom e0) :=
    ⟨⟨hover, hI, hEq⟩, rfl⟩
  -- (the `Smooth` instance is passed by hand: `MD'.X.left` is `(disjoinSeq T.E).last` only up to
  -- unfolding, so instance search does not see `hsm` there)
  have hcs := (dimFreeBMO_commutesWithSmooth stage0 1 (k := k)).1
  have hC : (dimFreeBMO stage0 1 k).seq ⟨T, 1⟩ ⟨le_rfl, rfl⟩ = R.pullback (eqToHom e0) := by
    rw [hB]
    exact @hcs MD' ⟨T, 1⟩ (eqToHom e0) hsm hsurj hpb ⟨le_rfl, rfl⟩ ⟨le_rfl, rfl⟩
  -- Step D: assemble; the output of `BMO_1` has no empty center
  have hne : (R.pullback (eqToHom e0)).NoEmptyCenters := by
    rw [← hC]
    exact (dimFreeBMO stage0 1 k).noEmptyCenters _ _
  rw [(eraseEmpty_eq_self_iff _).mpr hne]
  exact hC.symm

end Hironaka.Sequence
