/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Functoriality
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.UpToUnits
public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentFunctor
import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityPullback
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SmoothLoop
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SmoothStep3
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (2) of marked order reduction: smooth morphisms, and indifference to empty members

Clause (2) of [Kol07, Theorem 107] with both clauses of [Kol07, 34.1]: `BMO_{n,m}` commutes with
smooth morphisms. The first clause, for smooth surjections, is `commutesWithSmoothSurjections`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Functoriality.lean`); the second, for an
arbitrary smooth `h`, says that `BMO(Y, h^* I, m, h^{-1} E)` is obtained from the pull-back `h^*
BMO(X, I, m, E)` by deleting every blow-up whose centre is empty. The second clause is assembled
here from the loops (`step1_eraseEmpty_pullback`, `step2_eraseEmpty_pullback`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothLoop.lean`) and Step 3
(`step3Seq_eraseEmpty_pullback`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothStep3.lean`) through the tails of
`Functoriality.lean`, for the invariant "pull-back up to unit members" (`IsPullbackOfUpToUnits`),
under the indifference `hboind` of the input functors to unit boundary members:
`bmoSeq_eraseEmpty_pullback`. Its two uses:

* `commutesWithSmooth (hboind)`: the exact pull-back is a pull-back up to unit members
  (`IsPullbackOf.upToUnits`);
* `indifferentToEmptyMembers (hboind)` ([Kol07, 32] and the reindexing of [Kol07, 34.1] as a
  property of the functor): deleting unit members of the boundary is a pull-back up to unit
  members along the identity (`isPullbackOfUpToUnits_id`), and the pull-back along the identity
  with its empty blow-ups deleted is the sequence itself (`pullback_id`, `eraseEmpty_bmoSeq`).

The hypothesis `hboind` is discharged for the order-reduction data of dimension `n` in
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentGlobal.lean`; the fields are assembled
into `BMOData` in `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Theorem107.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}

/-- The tail after Step 2 under an arbitrary smooth morphism: if the Step-2 value on the pull-back
data up to unit members is the erased pull-back of the Step-2 value, so is the tail (Step 3),
along the last-stage isomorphism followed by the last-stage lift (`step3Seq_eraseEmpty_pullback`,
`IsPullbackOfUpToUnits.induced_eraseEmpty`). -/
theorem tailAfterStep2_eraseEmpty_pullback (T T' : MarkedTriple k)
    (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T')
    (τ : {R : BlowUpSequence T.X.left //
      R.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ R.NoEmptyCenters})
    (τ' : {R : BlowUpSequence T'.X.left //
      R.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E ∧ R.NoEmptyCenters})
    (e : τ'.1 = (τ.1.pullback h).eraseEmpty) :
    tailAfterStep2 T' hT' τ' = ((tailAfterStep2 T hT τ).pullback h).eraseEmpty := by
  obtain ⟨R', hR'⟩ := τ'
  dsimp only at e
  subst e
  have hq := hp.induced_eraseEmpty τ.2.1 hR'.1
  have hsc : Smooth (τ.1.pullback h).eraseEmptyLastHom := smooth_eraseEmptyLastHom' _
  have hsp : Smooth (τ.1.pullbackLastHom h) := smooth_pullbackLastHom _ h
  have hsmq : @Smooth (T'.induced (τ.1.pullback h).eraseEmpty hR'.1 (Fin.last _)).X.left
      (T.induced τ.1 τ.2.1 (Fin.last _)).X.left
      ((τ.1.pullback h).eraseEmptyLastHom ≫ τ.1.pullbackLastHom h) :=
    inferInstanceAs (Smooth ((τ.1.pullback h).eraseEmptyLastHom ≫ τ.1.pullbackLastHom h))
  have h3 := step3Seq_eraseEmpty_pullback (T.induced τ.1 τ.2.1 (Fin.last _))
    (T'.induced (τ.1.pullback h).eraseEmpty hR'.1 (Fin.last _)) _ hq
    (MarkedTriple.bmoClass_induced T hT τ.2.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hR'.1 (Fin.last _))
  have hQ : ((step3Seq (T.induced τ.1 τ.2.1 (Fin.last _))
        (MarkedTriple.bmoClass_induced T hT τ.2.1 (Fin.last _))).pullback
          ((τ.1.pullback h).eraseEmptyLastHom ≫ τ.1.pullbackLastHom h)).eraseEmpty =
      (((step3Seq (T.induced τ.1 τ.2.1 (Fin.last _))
        (MarkedTriple.bmoClass_induced T hT τ.2.1 (Fin.last _))).pullback
          (τ.1.pullbackLastHom h)).eraseEmpty).pullback (τ.1.pullback h).eraseEmptyLastHom :=
    (congrArg BlowUpSequence.eraseEmpty (pullback_comp _ _ _)).trans
      (eraseEmpty_pullback_of_flat_surjective _ _ (surjective_of_isIso _))
  dsimp only [tailAfterStep2]
  refine Eq.trans ?_ ((congrArg BlowUpSequence.eraseEmpty (pullback_concat _ _ h)).trans
    (eraseEmpty_concat _ _)).symm
  exact congrArg (τ.1.pullback h).eraseEmpty.concat (h3.trans hQ)

/-- The tail after Step 1 under an arbitrary smooth morphism: the tail (Steps 2 and 3) on the
erased pull-back of a Step-1 value is the erased pull-back of the tail along the last-stage lift,
carried along the last-stage isomorphism (`step2_eraseEmpty_pullback` on the induced marked
triples, then `tailAfterStep2_eraseEmpty_pullback`). -/
theorem tailAfterStep1_eraseEmpty_pullback
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (S : BlowUpSequence T.X.left)
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters)
    (hS' : (S.pullback h).eraseEmpty.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E ∧
      (S.pullback h).eraseEmpty.NoEmptyCenters) :
    tailAfterStep1 bo T' hT' ⟨(S.pullback h).eraseEmpty, hS'⟩ =
      (((tailAfterStep1 bo T hT ⟨S, hS⟩).pullback (S.pullbackLastHom h)).eraseEmpty).pullback
        (S.pullback h).eraseEmptyLastHom := by
  have hq := hp.induced_eraseEmpty hS.1 hS'.1
  have hsc : Smooth (S.pullback h).eraseEmptyLastHom := smooth_eraseEmptyLastHom' _
  have hsp : Smooth (S.pullbackLastHom h) := smooth_pullbackLastHom _ h
  have hsmq : @Smooth (T'.induced (S.pullback h).eraseEmpty hS'.1 (Fin.last _)).X.left
      (T.induced S hS.1 (Fin.last _)).X.left
      ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) :=
    inferInstanceAs (Smooth ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h))
  have h2 := step2_eraseEmpty_pullback bo hboind (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback h).eraseEmpty hS'.1 (Fin.last _)) _ hq
    (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))
  have htail := tailAfterStep2_eraseEmpty_pullback (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback h).eraseEmpty hS'.1 (Fin.last _)) _ hq
    (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))
    (step2 bo (T.induced S hS.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _)))
    (step2 bo (T'.induced (S.pullback h).eraseEmpty hS'.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))) h2
  have hiso : IsIso (S.pullback h).eraseEmptyLastHom := isIso_eraseEmptyLastHom _
  have hfl : Flat (S.pullback h).eraseEmptyLastHom := inferInstance
  have hQ : ((tailAfterStep2 (T.induced S hS.1 (Fin.last _))
        (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
        (step2 bo (T.induced S hS.1 (Fin.last _))
          (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _)))).pullback
          ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h)).eraseEmpty =
      (((tailAfterStep2 (T.induced S hS.1 (Fin.last _))
        (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
        (step2 bo (T.induced S hS.1 (Fin.last _))
          (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _)))).pullback
          (S.pullbackLastHom h)).eraseEmpty).pullback (S.pullback h).eraseEmptyLastHom :=
    (congrArg BlowUpSequence.eraseEmpty (pullback_comp _ _ _)).trans
      (eraseEmpty_pullback_of_flat_surjective _ _ (surjective_of_isIso _))
  dsimp only [tailAfterStep1]
  exact htail.trans hQ

/-- The whole assembly under an arbitrary smooth morphism: if the Step-1 value on the pull-back
data up to unit members is the erased pull-back of the Step-1 value, the concatenation with the
tail is the erased pull-back of the concatenation (`pullback_concat`, `eraseEmpty_concat`,
`tailAfterStep1_eraseEmpty_pullback`). -/
theorem concat_tailAfterStep1_eraseEmpty_pullback
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T')
    (σ : {S : BlowUpSequence T.X.left //
      S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters})
    (σ' : {S : BlowUpSequence T'.X.left //
      S.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E ∧ S.NoEmptyCenters})
    (e : σ'.1 = (σ.1.pullback h).eraseEmpty) :
    σ'.1.concat (tailAfterStep1 bo T' hT' σ') =
      ((σ.1.concat (tailAfterStep1 bo T hT σ)).pullback h).eraseEmpty := by
  obtain ⟨S', hS'⟩ := σ'
  dsimp only at e
  subst e
  refine Eq.trans ?_ ((congrArg BlowUpSequence.eraseEmpty (pullback_concat _ _ h)).trans
    (eraseEmpty_concat _ _)).symm
  exact congrArg (σ.1.pullback h).eraseEmpty.concat
    (tailAfterStep1_eraseEmpty_pullback bo hboind T T' h hp hT hT' σ.1 σ.2 hS')

/-- **For a marked triple that is the pull-back of `T` up to unit boundary members along a smooth
`h`, `BMO_{n,m}` is the pull-back of `BMO_{n,m}(T)` with its empty blow-ups deleted** (the second
clause of [Kol07, 34.1]), under the indifference of the input functors: the skipped rounds and the
matched rounds of Steps 1–2, then Step 3, assembled through the tails. -/
theorem bmoSeq_eraseEmpty_pullback
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') :
    bmoSeq bo T' hT' = ((bmoSeq bo T hT).pullback h).eraseEmpty := by
  rw [bmoSeq_eq_concat_tailAfterStep1, bmoSeq_eq_concat_tailAfterStep1]
  exact concat_tailAfterStep1_eraseEmpty_pullback bo hboind T T' h hp hT hT' (step1 bo T hT)
    (step1 bo T' hT') (step1_eraseEmpty_pullback bo hboind T T' h hp hT hT')

/-- **`BMO_{n,m}` commutes with smooth morphisms** (clause (2) of [Kol07, Theorem 107] with both
clauses of [Kol07, 34.1]), given the indifference of every input functor `bo d` to empty boundary
members (`hboind`): the surjective clause is `commutesWithSmoothSurjections`; for a general smooth
`h` the rounds of Steps 1–2 at parameters above `Y`'s pull back to empty blow-ups
(`pullback_eraseEmpty_eq_nil_of_maxOrd_lt`, the skipped-round argument), leaving unit boundary
members that only `hboind` lets the two runs ignore, and Step 3 is `realize_pullback_eraseEmpty`. -/
theorem commutesWithSmooth
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers) :
    (Hironaka.BMO.functor (k := k) bo m).CommutesWithSmooth := by
  refine ⟨commutesWithSmoothSurjections bo, ?_⟩
  intro T T' h _ hp hT hT'
  exact bmoSeq_eraseEmpty_pullback bo hboind T T' h hp.upToUnits hT hT'

/-- **`BMO_{n,m}` is indifferent to empty boundary members** ([Kol07, 32] and the reindexing of
[Kol07, 34.1] as a property of the functor), given the indifference of every input functor `bo d`
(`hboind`): deleting unit members of the boundary is a pull-back up to unit members along the
identity, so the run on the smaller boundary is the run on the larger one pulled back along the
identity and erased, that is, the run itself (`eraseEmpty_bmoSeq`). -/
theorem indifferentToEmptyMembers
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers) :
    (Hironaka.BMO.functor (k := k) bo m).IndifferentToEmptyMembers := by
  intro T E' hsnc' e hmem htop hT hT'
  have hsm : @Smooth ({ T with E := E', isSnc := hsnc' } : MarkedTriple k).X.left T.X.left
    (𝟙 T.X.left) :=
    Hironaka.BD.smooth_eqToHom rfl
  have key := bmoSeq_eraseEmpty_pullback bo hboind T { T with E := E', isSnc := hsnc' } (𝟙 T.X.left)
    (MarkedTriple.isPullbackOfUpToUnits_id T E' hsnc' e hmem htop) hT hT'
  rw [pullback_id, eraseEmpty_bmoSeq] at key
  exact key.symm

end Hironaka.BMO
