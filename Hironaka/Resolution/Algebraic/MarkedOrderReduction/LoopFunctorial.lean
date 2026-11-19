/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step2Separation
import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityPullback
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Parameters
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.EraseEmptyConcat
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of the loops of Steps 1 and 2 under smooth surjections

The first clause of [Kol07, 34.1] for Steps 1 and 2 of the proof of [Kol07, Theorem 107] ([Kol07,
111]: "the functoriality conditions are just as obvious as before"). Step 1 is the loop of the
rounds `BO_{n,d}(X, N(I), E)` on the marked triples induced after each round
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`), Step 2 the loop of
the rounds `BO_{n,ms}(X, N(I)^m + I^s, E)`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step2Separation.lean`). Each round commutes
with a smooth surjection by clause (2) of [Kol07, Theorem 103] (`BOData.commutesWithSmooth`, first
clause) on the pulled-back round triple, since `N(h^* I) = h^* N(I)` and the loop variables are
preserved (`roundOrder_of_isPullbackOf`, `sepOrder_of_isPullbackOf`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Parameters.lean`); and the marked triple induced
at the end of the pulled-back round carries the pull-back data of the triple induced at the end of
the round, along the last-stage lift (`MarkedTriple.isPullbackOf_induced_last`, the marked form of
`isPullbackOf_induced_last` of
`Hironaka/Resolution/Algebraic/OrderReduction/Step21Functorial.lean`). By induction over the
well-founded recursions (on a bound for the loop variable, as in
`maxOrd_nonmonomialPart_step1_lt_aux`), `step1` and `step2` commute with smooth surjections
(`step1_pullback_of_surjective`, `step2_pullback_of_surjective`): the pull-back of a concatenation
is the concatenation of the pull-backs (`pullback_concat`), the induced triples are transported
along the equality of the rounds (`MarkedTriple.isPullbackOf_induced_of_eq_seq`, absorbing the
`eqToHom`), and the concatenation is re-assembled by `concat_pullback_eqToHom`. Step 3 and the whole
functor are treated in `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Functorial.lean` and
`Functoriality.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.MarkedTriple

open Scheme

variable {k : Type u} [Field k]

/-- The marked triple induced at a stage of the pulled-back sequence carries the pull-back data of
the marked triple induced at that stage, along the stage lift, with the same mark (the marked form
of `IsPullbackOf.induced_isPullbackOf`; from the transport of marked transforms
`IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk` and `totalTransformSeq_pullback`). -/
theorem IsPullbackOf.induced_isPullbackOf [CharZero k] {T T' : MarkedTriple k}
    {h : T'.X.left ⟶ T.X.left} [Smooth h] (hp : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hS' : (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (i : Fin (S.length + 1)) :
    (T'.induced (S.pullback h) hS' (S.pullbackStageIdx h i)).IsPullbackOf (T.induced S hS i)
      (S.pullbackStageHom h i) := by
  obtain ⟨⟨hover, hI, hE⟩, hm⟩ := hp
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change S.pullbackStageHom h i ≫ (S.stageMap i ≫ (T.X.left ↘ Spec (.of k))) =
      (S.pullback h).stageMap (S.pullbackStageIdx h i) ≫ (T'.X.left ↘ Spec (.of k))
    rw [← Category.assoc, pullbackStageHom_stageMap, Category.assoc, hover]
  · change (S.pullback h).markedTransformSeq T'.I T'.m (S.pullbackStageIdx h i) =
      (S.markedTransformSeq T.I T.m i).comap (S.pullbackStageHom h i)
    rw [hI, hm]
    obtain ⟨j, hj⟩ := i
    exact IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk
      (T.X.left ↘ Spec (.of k)) n h hS j hj
  · change (S.pullback h).totalTransformSeq T'.E (S.pullbackStageIdx h i) =
      (S.totalTransformSeq T.E i).comap (S.pullbackStageHom h i)
    rw [hE]
    exact totalTransformSeq_pullback S h T.E i
  · exact hm

/-- Transport of pull-back data of an induced marked triple along an equality of stage indices: the
`eqToHom` of the stage identification is absorbed (the marked form of
`Triple.isPullbackOf_induced_of_eq_idx`). -/
theorem isPullbackOf_induced_of_eq_idx [CharZero k] {T' : MarkedTriple k}
    {S' : BlowUpSequence T'.X.left}
    {hS' : S'.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E}
    {i j : Fin (S'.length + 1)} (e : i = j) {R : MarkedTriple k} {q : S'.stage i ⟶ R.X.left}
    (hq : (T'.induced S' hS' i).IsPullbackOf R q) :
    (T'.induced S' hS' j).IsPullbackOf R (eqToHom (congrArg S'.stage e.symm) ≫ q) := by
  cases e
  exact hq

/-- The marked triple induced at the end of the pulled-back sequence is the pull-back of the marked
triple induced at the end of the sequence, along the last-stage lift (the marked form of
`isPullbackOf_induced_last`; the transport shared by both clauses of [Kol07, 34.1]). -/
theorem isPullbackOf_induced_last [CharZero k] {T T' : MarkedTriple k} (h : T'.X.left ⟶ T.X.left)
    [Smooth h] (hp : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hS' : (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E) :
    (T'.induced (S.pullback h) hS' (Fin.last _)).IsPullbackOf (T.induced S hS (Fin.last _))
      (S.pullbackLastHom h) :=
  isPullbackOf_induced_of_eq_idx (pullbackStageIdx_last S h)
    (hp.induced_isPullbackOf hS hS' (Fin.last _))

/-- Transport of pull-back data of the last induced marked triple along an equality of sequences:
the `eqToHom` of the last-stage identification is absorbed. -/
theorem isPullbackOf_induced_of_eq_seq [CharZero k] {T' : MarkedTriple k}
    {S S' : BlowUpSequence T'.X.left} (e : S = S')
    {hS : S.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E}
    {hS' : S'.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E} {R : MarkedTriple k}
    {q : S'.last ⟶ R.X.left} (hq : (T'.induced S' hS' (Fin.last _)).IsPullbackOf R q) :
    (T'.induced S hS (Fin.last _)).IsPullbackOf R
      (eqToHom (congrArg BlowUpSequence.last e) ≫ q) := by
  subst e
  exact hq

end Hironaka.MarkedTriple

namespace Hironaka.BMO

section Cast

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- The value of `BO_{n,d}` on a triple, transported along an equality of marks. -/
theorem functor_seq_cast {d d' : ℕ} (hdd : d = d') (N : Triple k) (p : Triple.BOClass n d N) :
    ((bo d).functor k).seq N p = ((bo d').functor k).seq N (hdd ▸ p) := by
  subst hdd
  rfl

end Cast

section Step1

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- The round triple `(X, N(I), E)` of the pull-back data is the pull-back of the round triple,
since `N(h^* I) = h^* N(I)`. -/
theorem nonmonomialTriple_isPullbackOf (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOf T h) : (nonmonomialTriple T').IsPullbackOf (nonmonomialTriple T) h :=
  ⟨hp.1.1, nonmonomialPart_comap T.toTriple h hp.1, hp.1.2.2⟩

/-- A round of Step 1 commutes with a smooth surjection (clause (2) of [Kol07, Theorem 103] with
the first clause of [Kol07, 34.1], per round): the round order is preserved and `BO_{n,d}`
commutes on the pulled-back round triple. -/
theorem step1Round_pullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (hd : m ≤ roundOrder T) (hd' : m ≤ roundOrder T') :
    step1Round bo T' hT' hd' = (step1Round bo T hT hd).pullback h := by
  have hr : roundOrder T' = roundOrder T := roundOrder_of_isPullbackOf T T' h hs hp
  have : @Smooth (nonmonomialTriple T').X.left (nonmonomialTriple T).X.left h := ‹Smooth h›
  rw [step1Round_eq, step1Round_eq, functor_seq_cast bo hr]
  exact ((bo (roundOrder T)).commutesWithSmooth k).1 (nonmonomialTriple T) (nonmonomialTriple T')
    h hs (nonmonomialTriple_isPullbackOf T T' h hp) _ _

/-- The induction behind `step1_pullback_of_surjective`: on a bound `l` for the loop variable,
following the recursion of `step1`. -/
theorem step1_pullback_of_surjective_aux (l : ℕ) :
    ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], Function.Surjective h →
      T'.IsPullbackOf T h → ∀ (hT : MarkedTriple.BMOClass n m T)
        (hT' : MarkedTriple.BMOClass n m T'), roundOrder T ≤ l →
          (step1 bo T' hT').1 = (step1 bo T hT).1.pullback h := by
  induction l with
  | zero =>
    intro T T' h _ hs hp hT hT' hl
    have hr : roundOrder T' = roundOrder T := roundOrder_of_isPullbackOf T T' h hs hp
    have hlt : roundOrder T < m := lt_of_le_of_lt hl hT.1
    rw [step1_of_lt bo T hT hlt, step1_of_lt bo T' hT' (hr ▸ hlt), pullback_nil]
  | succ l ih =>
    intro T T' h _ hs hp hT hT' hl
    have hr : roundOrder T' = roundOrder T := roundOrder_of_isPullbackOf T T' h hs hp
    by_cases hd : m ≤ roundOrder T
    · have hd' : m ≤ roundOrder T' := hr ▸ hd
      rw [step1_of_le bo T hT hd, step1_of_le bo T' hT' hd']
      refine Eq.trans ?_ (pullback_concat (step1Round bo T hT hd) _ h).symm
      have hR : step1Round bo T' hT' hd' = (step1Round bo T hT hd).pullback h :=
        step1Round_pullback bo T T' h hs hp hT hT' hd hd'
      have hsq : @Smooth (roundTriple bo T' hT' hd').X.left (roundTriple bo T hT hd).X.left
          (eqToHom (congrArg BlowUpSequence.last hR) ≫
            (step1Round bo T hT hd).pullbackLastHom h) :=
        MorphismProperty.comp_mem _ _ _ (Hironaka.BD.smooth_eqToHom _)
          (smooth_pullbackLastHom _ h)
      have hsurj : Function.Surjective (eqToHom (congrArg BlowUpSequence.last hR) ≫
          (step1Round bo T hT hd).pullbackLastHom h) := by
        have h1 : Surjective ((step1Round bo T hT hd).pullbackLastHom h) :=
          ⟨surjective_pullbackLastHom _ h hs⟩
        have h2 : Surjective (eqToHom (congrArg BlowUpSequence.last hR)) :=
          ⟨surjective_of_isIso _⟩
        exact (eqToHom (congrArg BlowUpSequence.last hR) ≫
          (step1Round bo T hT hd).pullbackLastHom h).surjective
      have hpb : (roundTriple bo T' hT' hd').IsPullbackOf (roundTriple bo T hT hd)
          (eqToHom (congrArg BlowUpSequence.last hR) ≫
            (step1Round bo T hT hd).pullbackLastHom h) :=
        MarkedTriple.isPullbackOf_induced_of_eq_seq hR
          (MarkedTriple.isPullbackOf_induced_last h hp (step1Round_isOrderGeSeq bo T hT hd)
            (hp.isOrderGeSeq_pullback (step1Round_isOrderGeSeq bo T hT hd)))
      have hih := ih (roundTriple bo T hT hd) (roundTriple bo T' hT' hd')
        (eqToHom (congrArg BlowUpSequence.last hR) ≫ (step1Round bo T hT hd).pullbackLastHom h)
        hsurj hpb (bmoClass_roundTriple bo T hT hd) (bmoClass_roundTriple bo T' hT' hd')
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo T hT hd) hl))
      exact (congrArg (step1Round bo T' hT' hd').concat (hih.trans (pullback_comp _ _ _))).trans
        (concat_pullback_eqToHom hR _)
    · have hlt : roundOrder T < m := not_le.mp hd
      rw [step1_of_lt bo T hT hlt, step1_of_lt bo T' hT' (hr ▸ hlt), pullback_nil]

/-- **Step 1 commutes with smooth surjections** (the first clause of [Kol07, 34.1] for Step 1):
round by round through the loop, by clause (2) of [Kol07, Theorem 103] on the pulled-back round
triples. -/
theorem step1_pullback_of_surjective (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') : (step1 bo T' hT').1 = (step1 bo T hT).1.pullback h :=
  step1_pullback_of_surjective_aux bo (roundOrder T) T T' h hs hp hT hT' le_rfl

end Step1

section Step2

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- The separating triple `(X, N(I)^m + I^s, E)` of the pull-back data is the pull-back of the
separating triple: `N(h^* I) = h^* N(I)`, the separation order is preserved, and the inverse image
commutes with sums and powers. -/
theorem sepTriple_isPullbackOf (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) :
    (sepTriple T').IsPullbackOf (sepTriple T) h := by
  obtain ⟨⟨hover, hI, hE⟩, hm⟩ := hp
  have hN : nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap h :=
    nonmonomialPart_comap T.toTriple h ⟨hover, hI, hE⟩
  have hsep : sepOrder T' = sepOrder T := sepOrder_of_isPullbackOf T T' h hs ⟨⟨hover, hI, hE⟩, hm⟩
  refine ⟨hover, ?_, hE⟩
  change sepIdeal T' = (sepIdeal T).comap h
  unfold sepIdeal
  rw [hN, hI, hm, hsep, IdealSheafData.comap_sup, IdealSheafData.comap_pow,
      IdealSheafData.comap_pow]

/-- A round of Step 2 commutes with a smooth surjection (clause (2) of [Kol07, Theorem 103] with
the first clause of [Kol07, 34.1], per round): the separation order is preserved and `BO_{n,ms}`
commutes on the pulled-back separating triple. -/
theorem step2Round_pullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (hpos : 0 < sepOrder T) (hpos' : 0 < sepOrder T') :
    step2Round bo T' hT' hpos' = (step2Round bo T hT hpos).pullback h := by
  have hr : T'.m * sepOrder T' = T.m * sepOrder T := by
    rw [hp.2, sepOrder_of_isPullbackOf T T' h hs hp]
  have : @Smooth (sepTriple T').X.left (sepTriple T).X.left h := ‹Smooth h›
  rw [step2Round_eq, step2Round_eq, functor_seq_cast bo hr]
  exact ((bo (T.m * sepOrder T)).commutesWithSmooth k).1 (sepTriple T) (sepTriple T') h hs
    (sepTriple_isPullbackOf T T' h hs hp) _ _

/-- The induction behind `step2_pullback_of_surjective`: on a bound `l` for the separation order,
following the recursion of `step2`. -/
theorem step2_pullback_of_surjective_aux (l : ℕ) :
    ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], Function.Surjective h →
      T'.IsPullbackOf T h → ∀ (hT : MarkedTriple.BMOClass n m T)
        (hT' : MarkedTriple.BMOClass n m T'), sepOrder T ≤ l →
          (step2 bo T' hT').1 = (step2 bo T hT).1.pullback h := by
  induction l with
  | zero =>
    intro T T' h _ hs hp hT hT' hl
    have hr : sepOrder T' = sepOrder T := sepOrder_of_isPullbackOf T T' h hs hp
    have h0 : sepOrder T = 0 := Nat.le_zero.mp hl
    rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo T' hT' (hr.trans h0), pullback_nil]
  | succ l ih =>
    intro T T' h _ hs hp hT hT' hl
    have hr : sepOrder T' = sepOrder T := sepOrder_of_isPullbackOf T T' h hs hp
    by_cases hpos : 0 < sepOrder T
    · have hpos' : 0 < sepOrder T' := hr ▸ hpos
      rw [step2_of_pos bo T hT hpos, step2_of_pos bo T' hT' hpos']
      refine Eq.trans ?_ (pullback_concat (step2Round bo T hT hpos) _ h).symm
      have hR : step2Round bo T' hT' hpos' = (step2Round bo T hT hpos).pullback h :=
        step2Round_pullback bo T T' h hs hp hT hT' hpos hpos'
      have hsq : @Smooth (step2Triple bo T' hT' hpos').X.left (step2Triple bo T hT hpos).X.left
          (eqToHom (congrArg BlowUpSequence.last hR) ≫
            (step2Round bo T hT hpos).pullbackLastHom h) :=
        MorphismProperty.comp_mem _ _ _ (Hironaka.BD.smooth_eqToHom _)
          (smooth_pullbackLastHom _ h)
      have hsurj : Function.Surjective (eqToHom (congrArg BlowUpSequence.last hR) ≫
          (step2Round bo T hT hpos).pullbackLastHom h) := by
        have h1 : Surjective ((step2Round bo T hT hpos).pullbackLastHom h) :=
          ⟨surjective_pullbackLastHom _ h hs⟩
        have h2 : Surjective (eqToHom (congrArg BlowUpSequence.last hR)) :=
          ⟨surjective_of_isIso _⟩
        exact (eqToHom (congrArg BlowUpSequence.last hR) ≫
          (step2Round bo T hT hpos).pullbackLastHom h).surjective
      have hpb : (step2Triple bo T' hT' hpos').IsPullbackOf (step2Triple bo T hT hpos)
          (eqToHom (congrArg BlowUpSequence.last hR) ≫
            (step2Round bo T hT hpos).pullbackLastHom h) :=
        MarkedTriple.isPullbackOf_induced_of_eq_seq hR
          (MarkedTriple.isPullbackOf_induced_last h hp (step2Round_isOrderGeSeq bo T hT hpos)
            (hp.isOrderGeSeq_pullback (step2Round_isOrderGeSeq bo T hT hpos)))
      have hih := ih (step2Triple bo T hT hpos) (step2Triple bo T' hT' hpos')
        (eqToHom (congrArg BlowUpSequence.last hR) ≫ (step2Round bo T hT hpos).pullbackLastHom h)
        hsurj hpb (bmoClass_step2Triple bo T hT hpos) (bmoClass_step2Triple bo T' hT' hpos')
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (sepOrder_step2Triple_lt bo T hT hpos) hl))
      exact (congrArg (step2Round bo T' hT' hpos').concat (hih.trans (pullback_comp _ _ _))).trans
        (concat_pullback_eqToHom hR _)
    · have h0 : sepOrder T = 0 := Nat.eq_zero_of_not_pos hpos
      rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo T' hT' (hr.trans h0), pullback_nil]

/-- **Step 2 commutes with smooth surjections** (the first clause of [Kol07, 34.1] for Step 2):
round by round through the loop, by clause (2) of [Kol07, Theorem 103] on the pulled-back
separating triples. -/
theorem step2_pullback_of_surjective (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') : (step2 bo T' hT').1 = (step2 bo T hT).1.pullback h :=
  step2_pullback_of_surjective_aux bo (sepOrder T) T T' h hs hp hT hT' le_rfl

end Step2

end Hironaka.BMO
