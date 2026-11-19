/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Data
public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentFunctor
import Hironaka.Resolution.Algebraic.BoundaryClearing.NilAtUnit
public import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentStep2
public import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Hironaka.Algebra.Local.TuningParam
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Scheme
import Hironaka.Scheme.Snc.Defs
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The globalised order-reduction functor is indifferent to empty boundary members

Kollár's convention [Kol07, 32] and the reindexing of [Kol07, 34.1] for the order-reduction functor
`BO_{n,m}` of [Kol07, Theorem 103] (`Hironaka.BO.functor`, the descent of the maximal-contact case
along the local covers of Step 3 of the proof): deleting unit-ideal members of the boundary does
not change its value. The identity is local. Both values pull back along the surjective
open-immersion coproduct `g : X^* → X` of a local cover (the same cover for both boundaries: the
inverse image keeps the index set, and the local class does not read the boundary) to the values
of the local functor (`functor_seq_pullback_localCover`), which are the maximal-contact case
`maxContactCase` for a common smooth hypersurface of maximal contact (`localFunctor_seq`); these
agree by `maxContactCase_indifferentToEmptyMembers` of
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentStep2.lean`, the deletion being pulled
back along `g` (`IsTopErasure.comap`); and pulling back along a surjective flat morphism is
injective on blow-up sequences (`pullback_injective_of_surjective`). The empty scheme is the
degenerate case, where every value is `nil`.

* `functor_indifferentToEmptyMembers`: the statement for `Hironaka.BO.functor n m bd`, under the
  two hypotheses on the boundary-clearing data of [Kol07, Lemma 102] at every mark, indifference to
  empty members (`hind`) and vanishing at a unit member (`hnil`).
* `data_indifferentToEmptyMembers`: the statement for the functor of `Hironaka.BO.data`, where the
  two hypotheses are discharged by `Hironaka.BD.bdData_indifferentToEmptyMembers` and
  `Hironaka.BD.bdData_nilAtUnitMember`, so that the conclusion holds under the indifference of the
  inductive input alone. This is the form used for the marked functor of [Kol07, Theorem 107]
  (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Theorem107.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Snc IsLocalRing

namespace Hironaka.Sequence

/-- A deletion of unit members with target `E₁` is one with target any family equal to `E₁`, the
embedding transported along the equality. -/
theorem IsTopErasure.of_eq {X : Scheme.{u}} {E' E₁ E₂ : DivisorFamily X} {e : E'.ι ↪o E₁.ι}
    (h : IsTopErasure E' E₁ e) (hEq : E₂ = E₁) : ∃ e₂ : E'.ι ↪o E₂.ι, IsTopErasure E' E₂ e₂ := by
  subst hEq
  exact ⟨e, h⟩

end Hironaka.Sequence

namespace Hironaka.BO

variable (n m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} n m j)

/-- **`BO_{n,m}` is indifferent to empty boundary members** ([Kol07, 32] and the reindexing of
[Kol07, 34.1] for the functor of [Kol07, Theorem 103]), over every field of characteristic zero,
under the hypotheses that the boundary-clearing data of [Kol07, Lemma 102] at every mark are
indifferent to empty members (`hind`) and nil at a unit member (`hnil`). By descent along a local
cover, the identity on the pieces being `maxContactCase_indifferentToEmptyMembers`. -/
theorem functor_indifferentToEmptyMembers
    (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    (hnil : ∀ m, BDFamily.NilAtUnitMember (bd m)) :
    ∀ (k : Type u) [Field k] [CharZero k],
      (Hironaka.BO.functor (k := k) n m bd).IndifferentToEmptyMembers := by
  intro k _ _ T E' hsnc' e hmem htop hT hT'
  by_cases hne : Nonempty T.X.left
  · obtain ⟨TU, g, hc⟩ := Triple.exists_isLocalCover (globalizationData_localClass n m) hT
    obtain ⟨-, hL, hM, hs, hcomp, hI, hE⟩ := hc
    have hsm : Smooth g := openImmersionCoprods.smooth hM
    have hfl : Flat g := openImmersionCoprods.flat hM
    have hsncF' : (E'.comap g).IsSnc := isSnc_comap_of_smooth (T.X.left ↘ Spec (.of k)) g hsnc'
    have hte : IsTopErasure E' T.E e := ⟨hmem, htop⟩
    obtain ⟨e₀, he₀⟩ := IsTopErasure.of_eq (hte.comap g) hE
    have hc₂ : Triple.IsLocalCover openImmersionCoprods (Triple.BOClass n m) (localClass n m)
        (T.withBoundary E' hsnc') (TU.withBoundary (E'.comap g) hsncF') g :=
      ⟨hT', hL, hM, hs, hcomp, hI, rfl⟩
    apply pullback_injective_of_surjective g hs
    rw [functor_seq_pullback_localCover n m bd ⟨hT, hL, hM, hs, hcomp, hI, hE⟩,
      functor_seq_pullback_localCover n m bd hc₂]
    obtain ⟨H, hH, hle⟩ := hL.2
    have hL₂ : localClass n m (TU.withBoundary (E'.comap g) hsncF') := hL
    have hle₂ : IdealSheafData.IsMaximalContact ((TU.withBoundary (E'.comap g) hsncF').X.left ↘ Spec
        (.of k))
        (TU.withBoundary (E'.comap g) hsncF').I m H := hle
    rw [localFunctor_seq n m bd TU hL hH hle,
      localFunctor_seq n m bd (TU.withBoundary (E'.comap g) hsncF') hL₂ hH hle₂]
    exact maxContactCase_indifferentToEmptyMembers TU hL.1 hH hle bd hind hnil (E'.comap g) hsncF'
      e₀ he₀.1 he₀.2 hL.1
  · have hemp : IsEmpty T.X.left := not_nonempty_iff.mp hne
    rw [BlowUpSequence.eq_nil_of_noEmptyCenters _
        ((Hironaka.BO.functor n m bd).noEmptyCenters T hT),
      BlowUpSequence.eq_nil_of_noEmptyCenters _
        ((Hironaka.BO.functor n m bd).noEmptyCenters _ hT')]

/-- **The functor of `Hironaka.BO.data` is indifferent to empty boundary members** ([Kol07, 32]
for the functor of [Kol07, Theorem 103]) under the indifference `hBind` of the inductive input
alone: `functor_indifferentToEmptyMembers` at the boundary-clearing data `Hironaka.BD.bdData`,
whose two hypotheses are `Hironaka.BD.bdData_indifferentToEmptyMembers` and
`Hironaka.BD.bdData_nilAtUnitMember`. -/
theorem data_indifferentToEmptyMembers
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type u) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers) :
    ∀ (k : Type u) [Field k] [CharZero k],
      ((Hironaka.BO.data n m Dom B hDom hB hsm hbc hBind).functor k).IndifferentToEmptyMembers :=
  functor_indifferentToEmptyMembers n m
    (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc)
    (fun m => Hironaka.BD.bdData_indifferentToEmptyMembers Dom B hDom hB hsm hbc hBind m)
    (fun m => Hironaka.BD.bdData_nilAtUnitMember n Dom B hDom hB hsm hbc m)

end Hironaka.BO
