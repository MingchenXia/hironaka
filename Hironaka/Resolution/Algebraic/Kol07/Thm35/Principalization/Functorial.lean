/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.TriplePullback
public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The principalization sequence commutes with smooth morphisms and with change of fields

Clause (4) of [Kol07, Theorem 35]: the principalization commutes with smooth morphisms
([Kol07, 34.1], both clauses: with smooth surjections outright, and with a general smooth morphism
up to the deletion of empty blow-ups) and with change of fields [Kol07, 34.2]. "The functoriality
properties required in (35) follow from the corresponding functoriality properties in (69)"
[Kol07, 72]: the definition `BP T = (disjoinSeq T.E ⧺ BMO_1(disjoinedTriple T)).eraseEmpty` is
built from two functorial pieces, so the proofs are assemblies.

* The disjoining sequence pulls back (`IsPullbackOf.disjoinSeq_eq`, `IsBaseChangeOf.disjoinSeq_eq`,
  from `disjoin_functorial` in `Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin/Functorial.lean`),
  and the disjoined triple of the pulled-back data is the pullback (resp. base change) of the
  disjoined triple along the lift `Triple.disjoinedMap` (`disjoinedTriple_isPullbackOf`,
  `disjoinedTriple_isBaseChangeOf`).
* The lift is smooth (`smooth_disjoinedMap`) and, over a surjection, surjective
  (`surjective_disjoinedMap`): it is a stage lift of the pullback through an `eqToHom`.
* So the functoriality of `BMO_1` ([Kol07, Theorem 69 (2)]; `dimFreeBMO_commutesWithSmooth`, both
  clauses, and `dimFreeBMO_commutesWithBaseChange`) identifies the `BMO_1` part of `BP T'` with
  the pullback of the `BMO_1` part of `BP T` along the lift.
* The concatenation pulls back piecewise (`pullback_concat`, the second piece along
  `pullbackLastHom`), the `eqToHom` of `disjoin_functorial` is absorbed
  (`concat_pullback_eqToHom`, `pullback_comp`), and the deletion of the empty blow-ups commutes
  with a flat surjective pullback (`eraseEmpty_pullback_of_flat_surjective`); for a general smooth
  `g` the second clause of 34.1 deletes them once more on both sides
  (`eraseEmpty_pullback_eraseEmpty'`, `eraseEmpty_concat_eraseEmpty`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Hironaka.Stage
  Hironaka.Sequence

namespace AlgebraicGeometry.Triple

open Hironaka

open Scheme

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L]

/-- The lift `disjoinedMap` of a smooth `g` is smooth (an `eqToHom` followed by the last-stage lift
of the pullback, `smooth_pullbackLastHom`). -/
theorem smooth_disjoinedMap {T : Triple k} {T' : Triple L} (g : T'.X.left ⟶ T.X.left) [Smooth g]
    (e : disjoinSeq T'.E = (disjoinSeq T.E).pullback g) : Smooth (disjoinedMap g e) :=
  MorphismProperty.comp_mem _ _ _ (Hironaka.BD.smooth_eqToHom _) (smooth_pullbackLastHom _ g)

/-- The lift `disjoinedMap` of a flat surjection is surjective (`surjective_pullbackLastHom`). -/
theorem surjective_disjoinedMap {T : Triple k} {T' : Triple L} (g : T'.X.left ⟶ T.X.left) [Flat g]
    (hs : Function.Surjective g) (e : disjoinSeq T'.E = (disjoinSeq T.E).pullback g) :
    Function.Surjective (disjoinedMap g e) := by
  have h1 : Surjective ((disjoinSeq T.E).pullbackLastHom g) :=
    ⟨surjective_pullbackLastHom _ g hs⟩
  have h2 : Surjective (eqToHom (congrArg BlowUpSequence.last e)) := ⟨surjective_of_isIso _⟩
  exact (eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom g).surjective

end AlgebraicGeometry.Triple

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- Clause (4) of [Kol07, Theorem 35], the first clause of [Kol07, 34.1]: `BP` commutes with smooth
surjections carrying the pullback data. -/
theorem BP_pullback_of_surjective (T T' : Triple k) (g : T'.X.left ⟶ T.X.left) [Smooth g]
    (hs : Function.Surjective g) (h : T'.IsPullbackOf T g) : BP T' = (BP T).pullback g := by
  have e : disjoinSeq T'.E = (disjoinSeq T.E).pullback g := h.disjoinSeq_eq
  have hsm : Smooth (Triple.disjoinedMap g e) := Triple.smooth_disjoinedMap g e
  have hsurj : Function.Surjective (Triple.disjoinedMap g e) :=
    Triple.surjective_disjoinedMap g hs e
  have hpb : (⟨disjoinedTriple T', 1⟩ : MarkedTriple k).IsPullbackOf
      ⟨disjoinedTriple T, 1⟩ (Triple.disjoinedMap g e) :=
    ⟨Triple.disjoinedTriple_isPullbackOf g h, rfl⟩
  have hcs := (dimFreeBMO_commutesWithSmooth stage0 1 (k := k)).1
  have hR : (dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T', 1⟩ ⟨le_rfl, rfl⟩ =
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩).pullback
        (Triple.disjoinedMap g e) :=
    @hcs ⟨disjoinedTriple T, 1⟩ ⟨disjoinedTriple T', 1⟩
      (Triple.disjoinedMap g e) hsm hsurj hpb ⟨le_rfl, rfl⟩ ⟨le_rfl, rfl⟩
  change ((disjoinSeq T'.E).concat
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T', 1⟩
          ⟨le_rfl, rfl⟩)).eraseEmpty =
    (((disjoinSeq T.E).concat
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩
        ⟨le_rfl, rfl⟩)).eraseEmpty).pullback g
  -- (`pullback_concat` instantiated by hand: the second piece lives on
  -- `(disjoinedTriple T).X.left`,
  -- which is `(disjoinSeq T.E).last` only by unfolding)
  have hpc := pullback_concat (disjoinSeq T.E)
    ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩) g
  rw [← eraseEmpty_pullback_of_flat_surjective _ g hs, hpc, hR]
  -- `disjoinedMap g e` is `eqToHom … ≫ pullbackLastHom g` by definition; `pullback_comp` splits the
  -- pullback along it and `concat_pullback_eqToHom` absorbs the `eqToHom` (instantiated by hand,
  -- the objects agreeing only by unfolding)
  exact congrArg BlowUpSequence.eraseEmpty ((congrArg (fun Q => (disjoinSeq T'.E).concat Q)
    (pullback_comp
        ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)
      (eqToHom (congrArg BlowUpSequence.last e)) ((disjoinSeq T.E).pullbackLastHom g))).trans
    (concat_pullback_eqToHom e _))

/-- Clause (4) of [Kol07, Theorem 35], the second clause of [Kol07, 34.1]: for every smooth `g`
carrying the pullback data, `BP T'` is the pullback `g^* BP T` with its empty blow-ups deleted. -/
theorem BP_pullback_eraseEmpty (T T' : Triple k) (g : T'.X.left ⟶ T.X.left) [Smooth g]
    (h : T'.IsPullbackOf T g) : BP T' = ((BP T).pullback g).eraseEmpty := by
  have e : disjoinSeq T'.E = (disjoinSeq T.E).pullback g := h.disjoinSeq_eq
  have hsm : Smooth (Triple.disjoinedMap g e) := Triple.smooth_disjoinedMap g e
  have hpb : (⟨disjoinedTriple T', 1⟩ : MarkedTriple k).IsPullbackOf
      ⟨disjoinedTriple T, 1⟩ (Triple.disjoinedMap g e) :=
    ⟨Triple.disjoinedTriple_isPullbackOf g h, rfl⟩
  have hce := (dimFreeBMO_commutesWithSmooth stage0 1 (k := k)).2
  have hR : (dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T', 1⟩ ⟨le_rfl, rfl⟩ =
      (((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩).pullback
        (Triple.disjoinedMap g e)).eraseEmpty :=
    @hce ⟨disjoinedTriple T, 1⟩ ⟨disjoinedTriple T', 1⟩
      (Triple.disjoinedMap g e) hsm hpb ⟨le_rfl, rfl⟩ ⟨le_rfl, rfl⟩
  change ((disjoinSeq T'.E).concat
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T', 1⟩
          ⟨le_rfl, rfl⟩)).eraseEmpty =
    ((((disjoinSeq T.E).concat
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩
        ⟨le_rfl, rfl⟩)).eraseEmpty).pullback g).eraseEmpty
  have hpc := pullback_concat (disjoinSeq T.E)
    ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩) g
  rw [eraseEmpty_pullback_eraseEmpty', hpc, hR]
  have h1 := eraseEmpty_concat_eraseEmpty (disjoinSeq T'.E)
    (((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩).pullback
      (Triple.disjoinedMap g e))
  exact h1.trans (congrArg BlowUpSequence.eraseEmpty
    ((congrArg (fun Q => (disjoinSeq T'.E).concat Q)
      (pullback_comp
          ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)
        (eqToHom (congrArg BlowUpSequence.last e)) ((disjoinSeq T.E).pullbackLastHom g))).trans
      (concat_pullback_eqToHom e _)))

/-- Clause (4) of [Kol07, Theorem 35], the change of fields of [Kol07, 34.2]: for `σ : k →+* L`
and a triple `T'` over `L` carrying the base-change data of `T`, `BP T'` is the pullback of `BP T`
along the projection. -/
theorem BP_baseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) (T : Triple k)
    (T' : Triple L) (p : T'.X.left ⟶ T.X.left)
    (h : T'.IsBaseChangeOf T σ p) : BP T' = (BP T).pullback p := by
  have hflat : Flat p := h.flat
  have hs : Function.Surjective p := h.surjective
  have e : disjoinSeq T'.E = (disjoinSeq T.E).pullback p := h.disjoinSeq_eq
  have hbc : (⟨disjoinedTriple T', 1⟩ : MarkedTriple L).IsBaseChangeOf
      ⟨disjoinedTriple T, 1⟩ σ (Triple.disjoinedMap p e) :=
    ⟨Triple.disjoinedTriple_isBaseChangeOf σ p h, rfl⟩
  have hR : (dimFreeBMO stage0 1 L).seq ⟨disjoinedTriple T', 1⟩ ⟨le_rfl, rfl⟩ =
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩).pullback
        (Triple.disjoinedMap p e) :=
    dimFreeBMO_commutesWithBaseChange stage0 1 σ ⟨disjoinedTriple T, 1⟩
      ⟨disjoinedTriple T', 1⟩ (Triple.disjoinedMap p e) hbc ⟨le_rfl, rfl⟩
          ⟨le_rfl, rfl⟩
  change ((disjoinSeq T'.E).concat
      ((dimFreeBMO stage0 1 L).seq ⟨disjoinedTriple T', 1⟩
          ⟨le_rfl, rfl⟩)).eraseEmpty =
    (((disjoinSeq T.E).concat
      ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩
        ⟨le_rfl, rfl⟩)).eraseEmpty).pullback p
  have hpc := pullback_concat (disjoinSeq T.E)
    ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩) p
  rw [← eraseEmpty_pullback_of_flat_surjective _ p hs, hpc, hR]
  exact congrArg BlowUpSequence.eraseEmpty ((congrArg (fun Q => (disjoinSeq T'.E).concat Q)
    (pullback_comp
        ((dimFreeBMO stage0 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)
      (eqToHom (congrArg BlowUpSequence.last e)) ((disjoinSeq T.E).pullbackLastHom p))).trans
    (concat_pullback_eqToHom e _))

end Hironaka.Sequence
