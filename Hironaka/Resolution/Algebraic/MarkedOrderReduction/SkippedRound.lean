/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Resolution.Algebraic.Kol07.TopCenters
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The skipped round: a round of order reduction that pulls back to empty blow-ups

The second clause of [Kol07, 34.1], that the blow-up sequence of the pull-back along a smooth
`h : Y → X` is the pull-back of the blow-up sequence with the blow-ups of empty centre deleted,
for the loops of Steps 1 and 2 of the proof of [Kol07, Theorem 107] rests on the following
observation, not in the sources as such: a round of an order-`d` functor `B` on `X` whose
pull-back data on `Y` have `max-ord < d` pulls back to empty blow-ups only, and the pulled-back
end data are the data of `Y` up to unit boundary members. Every centre of the round lies at points
of order exactly `d` for the current ideal (condition (4) of [Kol07, Definition 66] at the generic
points, at every point by upper semicontinuity), whose smooth pull-backs have the same order, and
`Y` has none; once the earlier pulled-back centres are empty, the pulled-back ideal at the next
stage is the inverse image of `h^* I` along an isomorphism, again of order `< d`. So every
pulled-back centre is the unit ideal (`center_pullback_eq_top_of_forall_ord_lt`, by induction along
the round with the one-step transport `weakTransform_comap_of_orderAlong_of_equidim`), and the four
conclusions are those of `Hironaka/Resolution/Algebraic/Kol07/TopCenters.lean`: the erased pull-back
is the empty sequence, its composite is an isomorphism, the weak transform at its end is the inverse
image of `Y`'s ideal, and its end boundary is `Y`'s boundary with the unit exceptional members
appended (`IsTopErasure`, the shape of the indifference to empty boundary members). Only the order
condition of `B` enters; commutation of `B` with smooth morphisms is not assumed. Used in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothLoop.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  IdealSheafData BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- The core of the skipped-round argument: along a smooth blow-up sequence of order `d` for
`(X, I, E)`, if the pull-back of `I` along a smooth `h : Y ⟶ X` has order `< d` at every point of
`Y`, every centre of the pulled-back sequence is the unit ideal. The first because the points of
the centre have order `≥ d` for `I` and their preimages the same order for `h^* I`; the later ones
by induction on the tail, whose starting ideal is the inverse image of `h^* I` along the trivial
blow-up, of order `< d` again. -/
theorem center_pullback_eq_top_of_forall_ord_lt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
      (h : Y ⟶ X) [Smooth h] (n' : ℕ) [SmoothOfRelativeDimension n' (h ≫ f)]
      (S : BlowUpSequence X) {I : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ},
      S.IsOrderSeq f I E d → (∀ y : Y, (I.comap h).ord y < d) →
      ∀ i, (S.pullback h).center i = ⊤
  | _, _, _, _, _, _, _, _, _, nil _, _, _, _, _, _, i => i.elim0
  | X, Y, f, n, _, h, _, n', _, cons _ D rest, I, E, d, hS, hlt, i => by
    obtain ⟨⟨hD, -, hm⟩, ht⟩ :=
      (isOrderSeq_cons_iff (f := f) (I := I) (E := E) (m := d) D rest).1 hS
    have hsm : Smooth (D.subschemeι ≫ f) := hD
    -- the first pulled-back centre is empty
    have hc0 : D.comap h = ⊤ := by
      refine le_antisymm le_top (le_of_stalkIdeal_le fun y => ?_)
      have hy : y ∉ (D.comap h).support := by
        intro hy
        rw [mem_support_comap_iff_apply] at hy
        have h1 : (d : ℕ∞) ≤ I.ord (h y) :=
          (leOrdAlong_iff_forall_mem (I := I) (f := f) (n := n) D.support (d : ℕ∞)).1
            (fun η hη => (hm η hη).ge) _ hy
        rw [← ord_comap_of_smooth (I := I) h y] at h1
        exact absurd (hlt y) (not_lt.2 h1)
      rw [stalkIdeal_eq_top_of_notMem_support _ hy]
      exact le_top
    -- the tail: the same situation one stage up
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hZ' : Smooth ((D.comap h).subschemeι ≫ h ≫ f) := smooth_subschemeι_comap_comp D h f
    have hsq : Scheme.Hom.blowUpMap h D ≫ D.blowUpπ ≫ f = (D.comap h).blowUpπ ≫ h ≫ f :=
        by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ f) (blowUpMap_π h D)
    have hπ' : SmoothOfRelativeDimension n' (Scheme.Hom.blowUpMap h D ≫ D.blowUpπ ≫ f) := by
      rw [hsq]
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth (h ≫ f) n' (D.comap h)
    have hsmb : Smooth (Scheme.Hom.blowUpMap h D) :=
      property_of_isPullback _ (isPullback_blowUpMap h D)
        inferInstance
    have hlt' : ∀ y₁ : (D.comap h).blowUp,
        ((I.weakTransform D).comap (Scheme.Hom.blowUpMap h D)).ord y₁ < d := by
      intro y₁
      rw [← weakTransform_comap_of_orderAlong_of_equidim f n h n' D I hm]
      have hy : y₁ ∉ (D.comap h).exceptionalDivisor.support := by
        intro hmem
        have hmem' := (mem_support_comap_iff_apply (D.comap h) (D.comap h).blowUpπ y₁).1 hmem
        have hsupp : (D.comap h).support = ⊥ := by
          rw [hc0]
          exact Scheme.IdealSheafData.support_top
        rw [hsupp] at hmem'
        have hmem'' : ((D.comap h).blowUpπ y₁ : Y) ∈ ((⊥ : Closeds Y) : Set Y) := hmem'
        rw [Closeds.coe_bot] at hmem''
        exact Set.notMem_empty _ hmem''
      rw [ord_weakTransform_of_notMem (D.comap h) (I.comap h) hy]
      exact hlt _
    rcases i with ⟨_ | j, hj⟩
    · exact hc0
    · exact center_pullback_eq_top_of_forall_ord_lt (D.blowUpπ ≫ f) n
        (Scheme.Hom.blowUpMap h D) n' rest
        ht hlt' ⟨j, Nat.lt_of_succ_lt_succ hj⟩

end Hironaka.Sequence

namespace Hironaka.BMO

open Hironaka.Sequence AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- **A round of an order-`d` functor on `X` whose pull-back to `Y` has `max-ord < d` pulls back to
empty blow-ups only, and the pulled-back end data are the data of `Y` up to unit boundary
members** (the second clause of [Kol07, 34.1], for one round): every centre of the round lies at
points of order `d` for the current ideal, whose smooth pull-backs have the same order, and `Y`
has none; so after deleting the empty blow-ups the pulled-back round is the empty sequence, its
composite is an isomorphism, the weak transform at its end is the pull-back of `Y`'s ideal, and its
end boundary is `Y`'s boundary with the unit exceptional divisors of the empty blow-ups appended
(`IsTopErasure`). Only the order condition of `B` enters. -/
theorem pullback_eraseEmpty_eq_nil_of_maxOrd_lt {d : ℕ} {Dom : Triple k → Prop}
    (B : OrderSeqAssignment k d Dom) (T T' : Triple k) (h : T'.X.left ⟶ T.X.left)
    [Smooth h] (hp : T'.IsPullbackOf T h) (hT : Dom T) (hlt : T'.I.maxOrd < (d : ℕ∞)) :
    ((B.seq T hT).pullback h).eraseEmpty = BlowUpSequence.nil T'.X.left ∧
      IsIso ((B.seq T hT).pullback h).composite ∧
      ((B.seq T hT).pullback h).weakTransformSeq T'.I (Fin.last _) =
        T'.I.comap ((B.seq T hT).pullback h).composite ∧
      ∃ e : T'.E.ι ↪o (((B.seq T hT).pullback h).totalTransformSeq T'.E (Fin.last _)).ι,
        IsTopErasure (T'.E.comap ((B.seq T hT).pullback h).composite)
          (((B.seq T hT).pullback h).totalTransformSeq T'.E (Fin.last _)) e := by
  obtain ⟨hover, hI, hE⟩ := hp
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  have hn'' : SmoothOfRelativeDimension n' (h ≫ (T.X.left ↘ Spec (.of k))) := by
    rw [hover]
    exact hn'
  have hlt' : ∀ y : T'.X.left, (T.I.comap h).ord y < d := fun y => by
    rw [← hI]
    exact lt_of_le_of_lt (le_maxOrd (I := T'.I) y) hlt
  have hc : ∀ i, ((B.seq T hT).pullback h).center i = ⊤ :=
    center_pullback_eq_top_of_forall_ord_lt (T.X.left ↘ Spec (.of k)) n h n' (B.seq T hT)
      (B.isOrderSeq T hT) hlt'
  rw [hI]
  refine ⟨eraseEmpty_eq_nil _ hc, isIso_composite_of_center_eq_top _ hc,
    weakTransformSeq_last_eq_comap_composite_of_center_eq_top _ _ hc, ?_⟩
  rw [hE]
  exact exists_isTopErasure_totalTransformSeq_of_center_eq_top _ (T.E.comap h) hc

end Hironaka.BMO
