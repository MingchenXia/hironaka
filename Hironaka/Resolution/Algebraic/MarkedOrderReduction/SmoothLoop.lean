/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.UpToUnits
public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentFunctor
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
public import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityPullback
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Clause1
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Clause3
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.LoopFunctorial
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SkippedRound
import Hironaka.Resolution.Algebraic.Order.SupPow
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loops of Steps 1 and 2 under an arbitrary smooth morphism

The second clause of [Kol07, 34.1] for the loops of the proof of [Kol07, Theorem 107]: along a
smooth `h : Y → X`, not necessarily surjective, Step 1 on the data of `Y` is the pull-back of
Step 1 on `X` with its empty blow-ups deleted, under the indifference of the input functors `bo d`
to unit boundary members (`hboind`). The induction runs over the recursion of `step1` on `X` with
the invariant "`T'` is the pull-back of `T` up to unit members" (`IsPullbackOfUpToUnits`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/UpToUnits.lean`). At a round of `X` at order
`d`:

* if the round order of `Y` is also `d`, the round on `Y` is the erased pull-back of the round on
  `X`: `hboind` moves the round from `(Y, N(I'), E')` to the round triple of the full pull-back
  (unit members appended, `nonmonomialTriple_fullPullback`), on which the second clause of
  [Kol07, 34.1] for [Kol07, Theorem 103] applies (`step1Round_eraseEmpty_pullback_of_eq`);
* if the round order of `Y` is smaller, the round is skipped: its pull-back consists of empty
  blow-ups (`pullback_eraseEmpty_eq_nil_of_maxOrd_lt`,
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/SkippedRound.lean`), and `Y`'s data are
  unchanged up to the isomorphism of the erased sequence with the empty
  sequence, along which `step1` is transported by the surjective clause
  (`step1_pullback_of_surjective` at the identity, `step1_induced_eq_seq`).

In both cases the marked triple induced on `Y` after the erased pulled-back round is the pull-back
up to unit members of the triple induced on `X` after the round
(`IsPullbackOfUpToUnits.induced_eraseEmpty`), and the induction closes with `pullback_concat`,
`eraseEmpty_concat` and the erasure along the last-stage isomorphism
(`eraseEmpty_pullback_of_flat_surjective`). Step 2 is the same argument on the separation order,
the skipped round bounded by `maxOrd_comap_sepIdeal_lt` (Kollár's observation in
[Kol07, 111, Step 2] that `ord (N^m + I^s) ≥ ms` iff `ord N ≥ s` and `ord I ≥ m`). The whole
functor is treated in `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Smooth.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

section Congr

/-- The value of `step1` on the marked triple induced at the end of a sequence, transported along
an equality of sequences (the `eqToHom` of the last-stage identification). -/
theorem step1_induced_eq_seq (T' : MarkedTriple k) {S₁ S₂ : BlowUpSequence T'.X.left} (e : S₁ = S₂)
    (h₁ : S₁.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (h₂ : S₂.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (c₁ : MarkedTriple.BMOClass n m (T'.induced S₁ h₁ (Fin.last _)))
    (c₂ : MarkedTriple.BMOClass n m (T'.induced S₂ h₂ (Fin.last _))) :
    (step1 bo (T'.induced S₁ h₁ (Fin.last _)) c₁).1 =
      ((step1 bo (T'.induced S₂ h₂ (Fin.last _)) c₂).1).pullback
        (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  exact (pullback_id _).symm

/-- The value of `step2` on the marked triple induced at the end of a sequence, transported along
an equality of sequences. -/
theorem step2_induced_eq_seq (T' : MarkedTriple k) {S₁ S₂ : BlowUpSequence T'.X.left} (e : S₁ = S₂)
    (h₁ : S₁.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (h₂ : S₂.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (c₁ : MarkedTriple.BMOClass n m (T'.induced S₁ h₁ (Fin.last _)))
    (c₂ : MarkedTriple.BMOClass n m (T'.induced S₂ h₂ (Fin.last _))) :
    (step2 bo (T'.induced S₁ h₁ (Fin.last _)) c₁).1 =
      ((step2 bo (T'.induced S₂ h₂ (Fin.last _)) c₂).1).pullback
        (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  exact (pullback_id _).symm

/-- A marked triple is the exact pull-back, along the identity, of the marked triple induced by the
empty sequence. -/
theorem isPullbackOf_induced_nil (T' : MarkedTriple k) :
    T'.IsPullbackOf (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _)
      (Fin.last _)) (𝟙 T'.X.left) := by
  refine ⟨⟨?_, (Scheme.IdealSheafData.comap_id _).symm, (DivisorFamily.comap_id _).symm⟩, rfl⟩
  change 𝟙 T'.X.left ≫ (𝟙 T'.X.left ≫ (T'.X.left ↘ Spec (.of k))) = T'.X.left ↘ Spec (.of k)
  rw [Category.id_comp, Category.id_comp]

/-- `step1` on a marked triple is `step1` on the marked triple induced by the empty sequence (the
surjective clause at the identity). -/
theorem step1_eq_step1_induced_nil (T' : MarkedTriple k) (hT' : MarkedTriple.BMOClass n m T') :
    (step1 bo T' hT').1 =
      (step1 bo (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _) (Fin.last _))
        (MarkedTriple.bmoClass_induced T' hT' _ (Fin.last _))).1 := by
  have hsm : @Smooth T'.X.left
      (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _)
      (Fin.last _)).X.left (𝟙 T'.X.left) :=
    Hironaka.BD.smooth_eqToHom rfl
  have := step1_pullback_of_surjective bo
    (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _)
    (Fin.last _)) T' (𝟙 T'.X.left)
    (surjective_of_isIso (𝟙 T'.X.left)) (isPullbackOf_induced_nil T')
    (MarkedTriple.bmoClass_induced T' hT' _ (Fin.last _)) hT'
  exact this.trans (pullback_id _)

/-- `step2` on a marked triple is `step2` on the marked triple induced by the empty sequence. -/
theorem step2_eq_step2_induced_nil (T' : MarkedTriple k) (hT' : MarkedTriple.BMOClass n m T') :
    (step2 bo T' hT').1 =
      (step2 bo (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _) (Fin.last _))
        (MarkedTriple.bmoClass_induced T' hT' _ (Fin.last _))).1 := by
  have hsm : @Smooth T'.X.left
      (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _)
      (Fin.last _)).X.left (𝟙 T'.X.left) :=
    Hironaka.BD.smooth_eqToHom rfl
  have := step2_pullback_of_surjective bo
    (T'.induced (BlowUpSequence.nil T'.X.left) (isOrderGeSeq_nil _ _ _ _)
    (Fin.last _)) T' (𝟙 T'.X.left)
    (surjective_of_isIso (𝟙 T'.X.left)) (isPullbackOf_induced_nil T')
    (MarkedTriple.bmoClass_induced T' hT' _ (Fin.last _)) hT'
  exact this.trans (pullback_id _)

end Congr

section Step1

/-- A round of Step 1 with matching round orders commutes with an arbitrary smooth morphism up to
empty blow-ups (clause (2) of [Kol07, Theorem 103] with the second clause of [Kol07, 34.1], per
round): the round of Step 1 on the pull-back data is the erased pull-back of the round; `hboind`
moves the round to the round triple of the full pull-back (unit members appended), on which the
second clause applies. -/
theorem step1Round_eraseEmpty_pullback_of_eq
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (hd : m ≤ roundOrder T) (hd' : m ≤ roundOrder T')
    (hr : roundOrder T' = roundOrder T) :
    step1Round bo T' hT' hd' = ((step1Round bo T hT hd).pullback h).eraseEmpty := by
  have hsm₁ : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  have hsm₂ : @Smooth (nonmonomialTriple (MarkedTriple.fullPullback T' T h)).X.left
    (nonmonomialTriple T).X.left h := ‹Smooth h›
  have hpf := MarkedTriple.fullPullback_isPullbackOf hp
  obtain ⟨e, he⟩ := hp.2.2.2
  have hle : (nonmonomialPart T'.I (T.E.comap h)).maxOrd ≤ ((roundOrder T : ℕ) : ℕ∞) := by
    rw [nonmonomialPart_of_extendsByEmpty T'.I he.extendsByEmpty, ← coe_roundOrder T', hr]
  have hcls_f : Triple.BOClass n (roundOrder T)
      (nonmonomialTriple (MarkedTriple.fullPullback T' T h)) :=
    ⟨hT.1.trans hd, hT'.2.1, hle⟩
  have hcls' : Triple.BOClass n (roundOrder T)
      ({ nonmonomialTriple (MarkedTriple.fullPullback T' T h) with
        E := T'.E, isSnc := T'.isSnc } : Triple k) :=
    ⟨hT.1.trans hd, hT'.2.1, hle⟩
  have hTT := MarkedTriple.nonmonomialTriple_fullPullback hp
  have h1 : ∀ c₁ : Triple.BOClass n (roundOrder T) (nonmonomialTriple T'),
      ((bo (roundOrder T)).functor k).seq (nonmonomialTriple T') c₁ =
        ((bo (roundOrder T)).functor k).seq _ hcls' :=
    fun c₁ => eq_of_heq (functor_seq_heq bo rfl hTT c₁ hcls')
  have h2 := hboind (roundOrder T) k (nonmonomialTriple (MarkedTriple.fullPullback T' T h)) T'.E
    T'.isSnc e he.1 he.2 hcls_f hcls'
  have h3 := ((bo (roundOrder T)).commutesWithSmooth k).2 (nonmonomialTriple T)
    (nonmonomialTriple (MarkedTriple.fullPullback T' T h)) h
    (nonmonomialTriple_isPullbackOf T (MarkedTriple.fullPullback T' T h) h hpf)
    (boClass_nonmonomialTriple T hT hd) hcls_f
  rw [step1Round_eq, step1Round_eq, functor_seq_cast bo hr]
  exact (h1 _).trans (h2.symm.trans h3)

/-- The skipped round of Step 1: when the round order of the pull-back data is smaller than the
round order of `X`, the round pulls back to empty blow-ups only
(`pullback_eraseEmpty_eq_nil_of_maxOrd_lt` at the round triples). -/
theorem step1Round_pullback_eraseEmpty_eq_nil (T T' : MarkedTriple k)
    (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hd : m ≤ roundOrder T) (hlt : roundOrder T' < roundOrder T) :
    ((step1Round bo T hT hd).pullback h).eraseEmpty = BlowUpSequence.nil T'.X.left := by
  have hsm₁ : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  have hsm₂ : @Smooth (nonmonomialTriple (MarkedTriple.fullPullback T' T h)).X.left
    (nonmonomialTriple T).X.left h := ‹Smooth h›
  have hpf := MarkedTriple.fullPullback_isPullbackOf hp
  obtain ⟨e, he⟩ := hp.2.2.2
  have hlt' : (nonmonomialTriple (MarkedTriple.fullPullback T' T h)).I.maxOrd <
      ((roundOrder T : ℕ) : ℕ∞) := by
    change (nonmonomialPart T'.I (T.E.comap h)).maxOrd < _
    rw [nonmonomialPart_of_extendsByEmpty T'.I he.extendsByEmpty, ← coe_roundOrder T']
    exact_mod_cast hlt
  exact (pullback_eraseEmpty_eq_nil_of_maxOrd_lt ((bo (roundOrder T)).functor k)
    (nonmonomialTriple T) (nonmonomialTriple (MarkedTriple.fullPullback T' T h)) h
    (nonmonomialTriple_isPullbackOf T (MarkedTriple.fullPullback T' T h) h hpf)
    (boClass_nonmonomialTriple T hT hd) hlt').1

/-- The induction behind `step1_eraseEmpty_pullback`: on a bound `l` for the round order of `X`,
following the recursion of `step1` on `X`, with the invariant "up to unit members". -/
theorem step1_eraseEmpty_pullback_aux
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers) (l : ℕ) :
    ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOfUpToUnits T h →
      ∀ (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T'),
        roundOrder T ≤ l → (step1 bo T' hT').1 = ((step1 bo T hT).1.pullback h).eraseEmpty := by
  induction l with
  | zero =>
    intro T T' h _ hp hT hT' hl
    have hlt : roundOrder T < m := lt_of_le_of_lt hl hT.1
    have hlt' : roundOrder T' < m := lt_of_le_of_lt hp.roundOrder_le hlt
    rw [step1_of_lt bo T hT hlt, step1_of_lt bo T' hT' hlt', pullback_nil, eraseEmpty_nil]
  | succ l ih =>
    intro T T' h _ hp hT hT' hl
    by_cases hd : m ≤ roundOrder T
    · obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
      have hsm₁ : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
      have hpf := MarkedTriple.fullPullback_isPullbackOf hp
      obtain ⟨e, he⟩ := hp.2.2.2
      have hR : (step1Round bo T hT hd).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
        step1Round_isOrderGeSeq bo T hT hd
      have hPf : ((step1Round bo T hT hd).pullback h).IsOrderGeSeq
          (T'.X.left ↘ Spec (.of k)) T'.I T'.m (T.E.comap h) := hpf.isOrderGeSeq_pullback hR
      have hP : ((step1Round bo T hT hd).pullback h).IsOrderGeSeq
          (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E := he.extendsByEmpty.isOrderGeSeq hPf
      have hP' : ((step1Round bo T hT hd).pullback h).eraseEmpty.IsOrderGeSeq
          (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E :=
        IsOrderGeSeq.eraseEmpty (T'.X.left ↘ Spec (.of k)) n' hP
      have hq := hp.induced_eraseEmpty hR hP'
      have hsc : Smooth ((step1Round bo T hT hd).pullback h).eraseEmptyLastHom :=
        smooth_eraseEmptyLastHom' _
      have hsp : Smooth ((step1Round bo T hT hd).pullbackLastHom h) := smooth_pullbackLastHom _ h
      have hsmq : @Smooth (T'.induced ((step1Round bo T hT hd).pullback h).eraseEmpty hP'
            (Fin.last _)).X.left (roundTriple bo T hT hd).X.left
          (((step1Round bo T hT hd).pullback h).eraseEmptyLastHom ≫
            (step1Round bo T hT hd).pullbackLastHom h) :=
        MorphismProperty.comp_mem @Smooth ((step1Round bo T hT hd).pullback h).eraseEmptyLastHom
          ((step1Round bo T hT hd).pullbackLastHom h) hsc hsp
      have hih := @ih (roundTriple bo T hT hd)
        (T'.induced ((step1Round bo T hT hd).pullback h).eraseEmpty hP' (Fin.last _))
        (((step1Round bo T hT hd).pullback h).eraseEmptyLastHom ≫
          (step1Round bo T hT hd).pullbackLastHom h) hsmq hq
        (bmoClass_roundTriple bo T hT hd) (MarkedTriple.bmoClass_induced T' hT' hP' (Fin.last _))
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo T hT hd) hl))
      have hQ : ((step1 bo (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)).1.pullback
            (((step1Round bo T hT hd).pullback h).eraseEmptyLastHom ≫
              (step1Round bo T hT hd).pullbackLastHom h)).eraseEmpty =
          (((step1 bo (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)).1.pullback
            ((step1Round bo T hT hd).pullbackLastHom h)).eraseEmpty).pullback
            ((step1Round bo T hT hd).pullback h).eraseEmptyLastHom :=
        (congrArg BlowUpSequence.eraseEmpty (pullback_comp _ _ _)).trans
          (eraseEmpty_pullback_of_flat_surjective _ _ (surjective_of_isIso _))
      have hih' := hih.trans hQ
      have hRHS : ((((step1Round bo T hT hd).concat
            (step1 bo (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)).1).pullback
              h).eraseEmpty) =
          ((step1Round bo T hT hd).pullback h).eraseEmpty.concat
            ((((step1 bo (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)).1.pullback
              ((step1Round bo T hT hd).pullbackLastHom h)).eraseEmpty).pullback
              ((step1Round bo T hT hd).pullback h).eraseEmptyLastHom) :=
        (congrArg BlowUpSequence.eraseEmpty (pullback_concat _ _ h)).trans (eraseEmpty_concat _ _)
      rw [step1_of_le bo T hT hd]
      refine Eq.trans ?_ hRHS.symm
      rcases hp.roundOrder_le.lt_or_eq with hlt | hr
      · -- the round of `X` is skipped on `Y`
        have hnil : ((step1Round bo T hT hd).pullback h).eraseEmpty =
          BlowUpSequence.nil T'.X.left :=
          step1Round_pullback_eraseEmpty_eq_nil bo T T' h hp hT hd hlt
        have hcongr := step1_induced_eq_seq bo T' hnil hP' (isOrderGeSeq_nil _ _ _ _)
          (MarkedTriple.bmoClass_induced T' hT' hP' (Fin.last _))
          (MarkedTriple.bmoClass_induced T' hT' _ (Fin.last _))
        have hstep0 := step1_eq_step1_induced_nil bo T' hT'
        calc (step1 bo T' hT').1
            = (BlowUpSequence.nil T'.X.left).concat (step1 bo T' hT').1 := rfl
          _ = ((step1Round bo T hT hd).pullback h).eraseEmpty.concat
                ((step1 bo T' hT').1.pullback (eqToHom (congrArg BlowUpSequence.last hnil))) :=
              (concat_pullback_eqToHom hnil _).symm
          _ = _ := congrArg ((step1Round bo T hT hd).pullback h).eraseEmpty.concat
              ((congrArg (fun P : BlowUpSequence T'.X.left =>
                P.pullback (eqToHom (congrArg BlowUpSequence.last hnil))) hstep0).trans
                (hcongr.symm.trans hih'))
      · -- the round of `X` is matched on `Y`
        have hd' : m ≤ roundOrder T' := hr ▸ hd
        have hR' : step1Round bo T' hT' hd' = ((step1Round bo T hT hd).pullback h).eraseEmpty :=
          step1Round_eraseEmpty_pullback_of_eq bo hboind T T' h hp hT hT' hd hd' hr
        rw [step1_of_le bo T' hT' hd']
        have hcongr := step1_induced_eq_seq bo T' hR' (step1Round_isOrderGeSeq bo T' hT' hd') hP'
          (bmoClass_roundTriple bo T' hT' hd')
          (MarkedTriple.bmoClass_induced T' hT' hP' (Fin.last _))
        exact (congrArg (step1Round bo T' hT' hd').concat (hcongr.trans (congrArg
          (fun P => P.pullback (eqToHom (congrArg BlowUpSequence.last hR'))) hih'))).trans
          (concat_pullback_eqToHom hR' _)
    · have hlt : roundOrder T < m := not_le.mp hd
      have hlt' : roundOrder T' < m := lt_of_le_of_lt hp.roundOrder_le hlt
      rw [step1_of_lt bo T hT hlt, step1_of_lt bo T' hT' hlt', pullback_nil, eraseEmpty_nil]

/-- **Step 1 on the pull-back data up to unit members is the pull-back of Step 1 with its empty
blow-ups deleted** (the second clause of [Kol07, 34.1] for Step 1), under the indifference of the
input functors. -/
theorem step1_eraseEmpty_pullback
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') :
    (step1 bo T' hT').1 = ((step1 bo T hT).1.pullback h).eraseEmpty :=
  step1_eraseEmpty_pullback_aux bo hboind (roundOrder T) T T' h hp hT hT' le_rfl

end Step1

section Step2

/-- The separating ideal of the full pull-back is the separating ideal of `T'`: unit members are
ignored by the split and by the separation order. -/
theorem sepIdeal_fullPullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) :
    sepIdeal (MarkedTriple.fullPullback T' T h) = sepIdeal T' := by
  obtain ⟨e, he⟩ := hp.2.2.2
  change nonmonomialPart T'.I (T.E.comap h) ^ T'.m ⊔
      T'.I ^ sepOrder (MarkedTriple.fullPullback T' T h) =
    nonmonomialPart T'.I T'.E ^ T'.m ⊔ T'.I ^ sepOrder T'
  rw [nonmonomialPart_of_extendsByEmpty T'.I he.extendsByEmpty,
    MarkedTriple.sepOrder_fullPullback hp]

/-- The separating triple of `T'` is the separating triple of its full pull-back with the unit
members deleted. -/
theorem sepTriple_fullPullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) :
    sepTriple T' =
      { T'.toTriple with
        I := sepIdeal (MarkedTriple.fullPullback T' T h)
        isNonzeroEverywhere := isNonzeroEverywhere_sepIdeal (MarkedTriple.fullPullback T' T h) } :=
  MarkedTriple.Triple_mk_I_congr T'.toTriple (sepIdeal_fullPullback T T' h hp).symm _ _

/-- The separating triple of an exact pull-back with the same separation order is the pull-back of
the separating triple (`sepTriple_isPullbackOf` without surjectivity). -/
theorem sepTriple_isPullbackOf_of_eq (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOf T h) (hsep : sepOrder T' = sepOrder T) :
    (sepTriple T').IsPullbackOf (sepTriple T) h := by
  obtain ⟨⟨hover, hI, hE⟩, hm⟩ := hp
  have hN : nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap h :=
    nonmonomialPart_comap T.toTriple h ⟨hover, hI, hE⟩
  refine ⟨hover, ?_, hE⟩
  change sepIdeal T' = (sepIdeal T).comap h
  unfold sepIdeal
  rw [hN, hI, hm, hsep, IdealSheafData.comap_sup, IdealSheafData.comap_pow,
      IdealSheafData.comap_pow]

/-- A round of Step 2 with matching separation orders commutes with an arbitrary smooth morphism
up to empty blow-ups (clause (2) of [Kol07, Theorem 103] with the second clause of [Kol07, 34.1],
per round): the round of Step 2 on the pull-back data is the erased pull-back of the round. -/
theorem step2Round_eraseEmpty_pullback_of_eq
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (hpos : 0 < sepOrder T) (hpos' : 0 < sepOrder T')
    (hs : sepOrder T' = sepOrder T) :
    step2Round bo T' hT' hpos' = ((step2Round bo T hT hpos).pullback h).eraseEmpty := by
  have hsm₁ : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  have hsm₂ : @Smooth (sepTriple (MarkedTriple.fullPullback T' T h)).X.left
    (sepTriple T).X.left h :=
    ‹Smooth h›
  have hpf := MarkedTriple.fullPullback_isPullbackOf hp
  obtain ⟨e, he⟩ := hp.2.2.2
  have hsepf : sepOrder (MarkedTriple.fullPullback T' T h) = sepOrder T :=
    (MarkedTriple.sepOrder_fullPullback hp).trans hs
  have hposf : 0 < sepOrder (MarkedTriple.fullPullback T' T h) := hsepf ▸ hpos
  have hr : T'.m * sepOrder T' = T.m * sepOrder T := by rw [hp.2.2.1, hs]
  have hrf : (MarkedTriple.fullPullback T' T h).m * sepOrder (MarkedTriple.fullPullback T' T h) =
      T.m * sepOrder T := by
    change T'.m * sepOrder (MarkedTriple.fullPullback T' T h) = T.m * sepOrder T
    rw [hsepf, hp.2.2.1]
  have hcls_f : Triple.BOClass n (T.m * sepOrder T)
      (sepTriple (MarkedTriple.fullPullback T' T h)) :=
    hrf ▸ boClass_sepTriple (MarkedTriple.fullPullback T' T h)
      (MarkedTriple.fullPullback_bmoClass hT') hposf
  have hcls' : Triple.BOClass n (T.m * sepOrder T)
      ({ sepTriple (MarkedTriple.fullPullback T' T h) with
        E := T'.E, isSnc := T'.isSnc } : Triple k) :=
    ⟨hcls_f.1, hT'.2.1, hcls_f.2.2⟩
  have hTT := sepTriple_fullPullback T T' h hp
  have h1 : ∀ c₁ : Triple.BOClass n (T.m * sepOrder T) (sepTriple T'),
      ((bo (T.m * sepOrder T)).functor k).seq (sepTriple T') c₁ =
        ((bo (T.m * sepOrder T)).functor k).seq _ hcls' :=
    fun c₁ => eq_of_heq (functor_seq_heq bo rfl hTT c₁ hcls')
  have h2 := hboind (T.m * sepOrder T) k (sepTriple (MarkedTriple.fullPullback T' T h)) T'.E
    T'.isSnc e he.1 he.2 hcls_f hcls'
  have h3 := ((bo (T.m * sepOrder T)).commutesWithSmooth k).2 (sepTriple T)
    (sepTriple (MarkedTriple.fullPullback T' T h)) h
    (sepTriple_isPullbackOf_of_eq T (MarkedTriple.fullPullback T' T h) h hpf hsepf)
    (boClass_sepTriple T hT hpos) hcls_f
  rw [step2Round_eq, step2Round_eq, functor_seq_cast bo hr]
  exact (h1 _).trans (h2.symm.trans h3)

/-- When the separation order of the pull-back data is smaller than that of `X`, the pulled-back
separating ideal `N(I')^m + I'^s` (with `X`'s `s`) has maximal order `< ms`: at a point of order
`≥ m` for `I'` the order of `N(I')` is at most the smaller separation order, and elsewhere
`ord I'^s < sm` (Kollár's observation in [Kol07, 111, Step 2]). -/
theorem maxOrd_comap_sepIdeal_lt (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T) (hpos : 0 < sepOrder T)
    (hlt : sepOrder T' < sepOrder T) :
    ((sepIdeal T).comap h).maxOrd < ((T.m * sepOrder T : ℕ) : ℕ∞) := by
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  have hs1 : 1 ≤ sepOrder T := hpos
  have hN := MarkedTriple.nonmonomialPart_eq_comap_of_upToUnits hp
  refine maxOrd_lt_of_forall_lt (Nat.mul_pos hm1 hpos) fun y => ?_
  rw [IdealSheafData.ord_comap_of_smooth]
  change (nonmonomialPart T.I T.E ^ T.m ⊔ T.I ^ sepOrder T).ord (h y) < _
  rw [← not_le, IdealSheafData.le_ord_pow_sup_pow_iff (T.X.left ↘ Spec (.of k)) n₀ _ _
    hm1 hs1 (h y)]
  rintro ⟨hN_le, hI_le⟩
  have hy : y ∈ {y | (T'.m : ℕ∞) ≤ T'.I.ord y} := by
    change (T'.m : ℕ∞) ≤ T'.I.ord y
    rw [hp.2.2.1, hp.2.1, IdealSheafData.ord_comap_of_smooth]
    exact hI_le
  have h1 : (nonmonomialPart T'.I T'.E).ord y ≤ (sepOrder T' : ℕ∞) := by
    rw [coe_sepOrder T']
    exact IdealSheafData.le_maxOrdAlong (I := nonmonomialPart T'.I T'.E) hy
  rw [hN, IdealSheafData.ord_comap_of_smooth] at h1
  have h2 : (sepOrder T : ℕ∞) ≤ (sepOrder T' : ℕ∞) := hN_le.trans h1
  exact absurd (by exact_mod_cast h2 : sepOrder T ≤ sepOrder T') (not_le.mpr hlt)

/-- The skipped round of Step 2: when the separation order of the pull-back data is smaller than
that of `X`, the round pulls back to empty blow-ups only. -/
theorem step2Round_pullback_eraseEmpty_eq_nil (T T' : MarkedTriple k)
    (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hpos : 0 < sepOrder T) (hlt : sepOrder T' < sepOrder T) :
    ((step2Round bo T hT hpos).pullback h).eraseEmpty = BlowUpSequence.nil T'.X.left := by
  have hflat : Flat h := inferInstance
  let P : Triple k :=
    { (MarkedTriple.fullPullback T' T h).toTriple with
      I := (sepIdeal T).comap h
      isNonzeroEverywhere := isNonzeroEverywhere_comap_of_flat h (isNonzeroEverywhere_sepIdeal T) }
  have hsmP : @Smooth P.X.left (sepTriple T).X.left h := ‹Smooth h›
  have hpP : P.IsPullbackOf (sepTriple T) h := ⟨hp.1, rfl, rfl⟩
  have hltP : P.I.maxOrd < ((T.m * sepOrder T : ℕ) : ℕ∞) :=
    maxOrd_comap_sepIdeal_lt T T' h hp hT hpos hlt
  exact (pullback_eraseEmpty_eq_nil_of_maxOrd_lt ((bo (T.m * sepOrder T)).functor k) (sepTriple T)
    P h hpP (boClass_sepTriple T hT hpos) hltP).1

/-- The induction behind `step2_eraseEmpty_pullback`: on a bound `l` for the separation order of
`X`, following the recursion of `step2` on `X`, with the invariant "up to unit members". -/
theorem step2_eraseEmpty_pullback_aux
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers) (l : ℕ) :
    ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOfUpToUnits T h →
      ∀ (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T'),
        sepOrder T ≤ l → (step2 bo T' hT').1 = ((step2 bo T hT).1.pullback h).eraseEmpty := by
  induction l with
  | zero =>
    intro T T' h _ hp hT hT' hl
    have h0 : sepOrder T = 0 := Nat.le_zero.mp hl
    have h0' : sepOrder T' = 0 := Nat.le_zero.mp (hp.sepOrder_le.trans hl)
    rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo T' hT' h0', pullback_nil, eraseEmpty_nil]
  | succ l ih =>
    intro T T' h _ hp hT hT' hl
    by_cases hpos : 0 < sepOrder T
    · obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
      have hsm₁ : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
      have hpf := MarkedTriple.fullPullback_isPullbackOf hp
      obtain ⟨e, he⟩ := hp.2.2.2
      have hR : (step2Round bo T hT hpos).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
        step2Round_isOrderGeSeq bo T hT hpos
      have hPf : ((step2Round bo T hT hpos).pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I
          T'.m (T.E.comap h) := hpf.isOrderGeSeq_pullback hR
      have hP : ((step2Round bo T hT hpos).pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I
          T'.m T'.E := he.extendsByEmpty.isOrderGeSeq hPf
      have hP' : ((step2Round bo T hT hpos).pullback h).eraseEmpty.IsOrderGeSeq
          (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E :=
        IsOrderGeSeq.eraseEmpty (T'.X.left ↘ Spec (.of k)) n' hP
      have hq := hp.induced_eraseEmpty hR hP'
      have hsc : Smooth ((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom :=
        smooth_eraseEmptyLastHom' _
      have hsp : Smooth ((step2Round bo T hT hpos).pullbackLastHom h) :=
        smooth_pullbackLastHom _ h
      have hsmq : @Smooth (T'.induced ((step2Round bo T hT hpos).pullback h).eraseEmpty hP'
            (Fin.last _)).X.left (step2Triple bo T hT hpos).X.left
          (((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom ≫
            (step2Round bo T hT hpos).pullbackLastHom h) :=
        MorphismProperty.comp_mem @Smooth ((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom
          ((step2Round bo T hT hpos).pullbackLastHom h) hsc hsp
      have hih := @ih (step2Triple bo T hT hpos)
        (T'.induced ((step2Round bo T hT hpos).pullback h).eraseEmpty hP' (Fin.last _))
        (((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom ≫
          (step2Round bo T hT hpos).pullbackLastHom h) hsmq hq
        (bmoClass_step2Triple bo T hT hpos) (MarkedTriple.bmoClass_induced T' hT' hP' (Fin.last _))
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (sepOrder_step2Triple_lt bo T hT hpos) hl))
      have hQ : ((step2 bo (step2Triple bo T hT hpos)
              (bmoClass_step2Triple bo T hT hpos)).1.pullback
            (((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom ≫
              (step2Round bo T hT hpos).pullbackLastHom h)).eraseEmpty =
          (((step2 bo (step2Triple bo T hT hpos) (bmoClass_step2Triple bo T hT hpos)).1.pullback
            ((step2Round bo T hT hpos).pullbackLastHom h)).eraseEmpty).pullback
            ((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom :=
        (congrArg BlowUpSequence.eraseEmpty (pullback_comp _ _ _)).trans
          (eraseEmpty_pullback_of_flat_surjective _ _ (surjective_of_isIso _))
      have hih' := hih.trans hQ
      have hRHS : ((((step2Round bo T hT hpos).concat
            (step2 bo (step2Triple bo T hT hpos) (bmoClass_step2Triple bo T hT hpos)).1).pullback
              h).eraseEmpty) =
          ((step2Round bo T hT hpos).pullback h).eraseEmpty.concat
            ((((step2 bo (step2Triple bo T hT hpos) (bmoClass_step2Triple bo T hT hpos)).1.pullback
              ((step2Round bo T hT hpos).pullbackLastHom h)).eraseEmpty).pullback
              ((step2Round bo T hT hpos).pullback h).eraseEmptyLastHom) :=
        (congrArg BlowUpSequence.eraseEmpty (pullback_concat _ _ h)).trans (eraseEmpty_concat _ _)
      rw [step2_of_pos bo T hT hpos]
      refine Eq.trans ?_ hRHS.symm
      rcases hp.sepOrder_le.lt_or_eq with hlt | hs
      · -- the round of `X` is skipped on `Y`
        have hnil : ((step2Round bo T hT hpos).pullback h).eraseEmpty =
          BlowUpSequence.nil T'.X.left :=
          step2Round_pullback_eraseEmpty_eq_nil bo T T' h hp hT hpos hlt
        have hcongr := step2_induced_eq_seq bo T' hnil hP' (isOrderGeSeq_nil _ _ _ _)
          (MarkedTriple.bmoClass_induced T' hT' hP' (Fin.last _))
          (MarkedTriple.bmoClass_induced T' hT' _ (Fin.last _))
        have hstep0 := step2_eq_step2_induced_nil bo T' hT'
        calc (step2 bo T' hT').1
            = (BlowUpSequence.nil T'.X.left).concat (step2 bo T' hT').1 := rfl
          _ = ((step2Round bo T hT hpos).pullback h).eraseEmpty.concat
                ((step2 bo T' hT').1.pullback (eqToHom (congrArg BlowUpSequence.last hnil))) :=
              (concat_pullback_eqToHom hnil _).symm
          _ = _ := congrArg ((step2Round bo T hT hpos).pullback h).eraseEmpty.concat
              ((congrArg (fun P : BlowUpSequence T'.X.left =>
                P.pullback (eqToHom (congrArg BlowUpSequence.last hnil))) hstep0).trans
                (hcongr.symm.trans hih'))
      · -- the round of `X` is matched on `Y`
        have hpos' : 0 < sepOrder T' := hs ▸ hpos
        have hR' : step2Round bo T' hT' hpos' = ((step2Round bo T hT hpos).pullback h).eraseEmpty :=
          step2Round_eraseEmpty_pullback_of_eq bo hboind T T' h hp hT hT' hpos hpos' hs
        rw [step2_of_pos bo T' hT' hpos']
        have hcongr := step2_induced_eq_seq bo T' hR' (step2Round_isOrderGeSeq bo T' hT' hpos') hP'
          (bmoClass_step2Triple bo T' hT' hpos')
          (MarkedTriple.bmoClass_induced T' hT' hP' (Fin.last _))
        exact (congrArg (step2Round bo T' hT' hpos').concat (hcongr.trans (congrArg
          (fun P => P.pullback (eqToHom (congrArg BlowUpSequence.last hR'))) hih'))).trans
          (concat_pullback_eqToHom hR' _)
    · have h0 : sepOrder T = 0 := Nat.eq_zero_of_not_pos hpos
      have h0' : sepOrder T' = 0 := Nat.le_zero.mp (hp.sepOrder_le.trans h0.le)
      rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo T' hT' h0', pullback_nil, eraseEmpty_nil]

/-- **Step 2 on the pull-back data up to unit members is the pull-back of Step 2 with its empty
blow-ups deleted** (the second clause of [Kol07, 34.1] for Step 2), under the indifference of the
input functors. -/
theorem step2_eraseEmpty_pullback
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') :
    (step2 bo T' hT').1 = ((step2 bo T hT).1.pullback h).eraseEmpty :=
  step2_eraseEmpty_pullback_aux bo hboind (sepOrder T) T T' h hp hT hT' le_rfl

end Step2

end Hironaka.BMO
