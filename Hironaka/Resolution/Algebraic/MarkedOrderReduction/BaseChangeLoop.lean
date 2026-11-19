/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Functoriality
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.BaseChangeParameters
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.LoopFunctorial
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Functorial
import Hironaka.Resolution.Algebraic.Monomial.Geometric.BaseChangeRealize
import Hironaka.Resolution.Algebraic.Monomial.Geometric.EnumerationIndep
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Refinement
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.BaseChangeTriple
import Hironaka.Scheme.BlowUpSequence.EraseEmptyConcat
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (2) of marked order reduction: change of fields

Clause (2) of [Kol07, Theorem 107] with [Kol07, 34.2]: for a field extension `σ : k → L` and the
base-changed marked triple `(X_L, I_L, m, E_L)` along the projection `p : X_L → X`,
`BMO_{n,m}(X_L, I_L, m, E_L) = p^* BMO_{n,m}(X, I, m, E)`; no blow-up is deleted, the projection
being surjective on points. The proof is the change-of-fields form of the argument for smooth
surjections (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/LoopFunctorial.lean`,
`Step3Functorial.lean`, `Functoriality.lean`): the round parameters are preserved
(`roundOrder_of_isBaseChangeOf`, `sepOrder_of_isBaseChangeOf`), each round commutes by the second
half of clause (2) of [Kol07, Theorem 103] (`BOData.commutesWithBaseChange`) on the base-changed
round triple, the marked triple induced at the end of the base-changed round carries the base-change
data of the one induced at the end of the round along the last-stage lift
(`MarkedTriple.isBaseChangeOf_induced_last`), the loops follow by induction over the well-founded
recursions, and Step 3 is
`realize_pullback_of_isBaseChangeOf`
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/BaseChangeRealize.lean`) on the refining family
`refinesAlong_ofDivisorFamily` in its flat form; the exponents agree at the generic points because
the order is preserved pointwise by a change of fields (`ord_comap_of_isBaseChangeOf`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Monomial Hironaka.Monomial.PieceFamily

namespace Hironaka.MarkedTriple

open Scheme

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-- Transport of base-change data of an induced marked triple along an equality of stage indices
(the marked form of `Triple.isBaseChangeOf_induced_of_eq_idx`). -/
theorem isBaseChangeOf_induced_of_eq_idx [CharZero L] {T' : MarkedTriple L}
    {S' : BlowUpSequence T'.X.left}
    {hS' : S'.IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E}
    {i j : Fin (S'.length + 1)} (e : i = j) {R : MarkedTriple k} {σ : k →+* L}
    {q : S'.stage i ⟶ R.X.left} (hq : (T'.induced S' hS' i).IsBaseChangeOf R σ q) :
    (T'.induced S' hS' j).IsBaseChangeOf R σ (eqToHom (congrArg S'.stage e.symm) ≫ q) := by
  cases e
  exact hq

/-- The marked triple induced at the end of the base-changed sequence is the base change of the
marked triple induced at the end of the sequence, along the last-stage lift ([Kol07, 34.2]; the
marked form of `isBaseChangeOf_induced_last`). -/
theorem isBaseChangeOf_induced_last [CharZero k] [CharZero L] {T : MarkedTriple k}
    {T' : MarkedTriple L} {σ : k →+* L} (p : T'.X.left ⟶ T.X.left) (hp : T'.IsBaseChangeOf T σ p)
    {S : BlowUpSequence T.X.left} (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hS' : (S.pullback p).IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E) :
    (T'.induced (S.pullback p) hS' (Fin.last _)).IsBaseChangeOf (T.induced S hS (Fin.last _)) σ
      (S.pullbackLastHom p) :=
  isBaseChangeOf_induced_of_eq_idx (pullbackStageIdx_last S p)
    (hp.induced_isBaseChangeOf hS hS' (Fin.last _))

/-- Transport of base-change data of the last induced marked triple along an equality of
sequences: the `eqToHom` of the last-stage identification is absorbed. -/
theorem isBaseChangeOf_induced_of_eq_seq [CharZero L] {T' : MarkedTriple L}
    {S S' : BlowUpSequence T'.X.left} (e : S = S')
    {hS : S.IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E}
    {hS' : S'.IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E} {R : MarkedTriple k}
    {σ : k →+* L} {q : S'.last ⟶ R.X.left}
    (hq : (T'.induced S' hS' (Fin.last _)).IsBaseChangeOf R σ q) :
    (T'.induced S hS (Fin.last _)).IsBaseChangeOf R σ
      (eqToHom (congrArg BlowUpSequence.last e) ≫ q) := by
  subst e
  exact hq

end Hironaka.MarkedTriple

namespace Hironaka.BMO

section Step1

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L] {n m : ℕ}
  (bo : ∀ d : ℕ, BOData.{u} n d)

/-- The round triple `(X, N(I), E)` of the base-changed data is the base change of the round
triple, since `N(I_L) = p^* N(I)`. -/
theorem nonmonomialTriple_isBaseChangeOf (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) :
    (nonmonomialTriple T').IsBaseChangeOf (nonmonomialTriple T) σ p :=
  ⟨hbc.1.1, nonmonomialPart_baseChange T.toTriple σ p hbc.1, hbc.1.2.2⟩

/-- A round of Step 1 commutes with a change of fields (clause (2) of [Kol07, Theorem 103] with
[Kol07, 34.2], per round): the round order is preserved and `BO_{n,d}` commutes on the base-changed
round triple. -/
theorem step1Round_baseChange (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (hd : m ≤ roundOrder T) (hd' : m ≤ roundOrder T') :
    step1Round bo T' hT' hd' = (step1Round bo T hT hd).pullback p := by
  have hr : roundOrder T' = roundOrder T := roundOrder_of_isBaseChangeOf T T' hbc
  rw [step1Round_eq, step1Round_eq, functor_seq_cast bo hr]
  exact (bo (roundOrder T)).commutesWithBaseChange k L σ (nonmonomialTriple T)
    (nonmonomialTriple T') p (nonmonomialTriple_isBaseChangeOf T T' σ p hbc) _ _

/-- The induction behind `step1_baseChange`: on a bound `l` for the loop variable, following the
recursion of `step1`. -/
theorem step1_baseChange_aux (σ : k →+* L) (l : ℕ) :
    ∀ (T : MarkedTriple k) (T' : MarkedTriple L)
    (p : T'.X.left ⟶ T.X.left), T'.IsBaseChangeOf T σ p →
      ∀ (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T'),
        roundOrder T ≤ l → (step1 bo T' hT').1 = (step1 bo T hT).1.pullback p := by
  induction l with
  | zero =>
    intro T T' p hbc hT hT' hl
    have hr : roundOrder T' = roundOrder T := roundOrder_of_isBaseChangeOf T T' hbc
    have hlt : roundOrder T < m := lt_of_le_of_lt hl hT.1
    rw [step1_of_lt bo T hT hlt, step1_of_lt bo T' hT' (hr ▸ hlt), pullback_nil]
  | succ l ih =>
    intro T T' p hbc hT hT' hl
    have hr : roundOrder T' = roundOrder T := roundOrder_of_isBaseChangeOf T T' hbc
    by_cases hd : m ≤ roundOrder T
    · have hd' : m ≤ roundOrder T' := hr ▸ hd
      rw [step1_of_le bo T hT hd, step1_of_le bo T' hT' hd']
      refine Eq.trans ?_ (pullback_concat (step1Round bo T hT hd) _ p).symm
      have hR : step1Round bo T' hT' hd' = (step1Round bo T hT hd).pullback p :=
        step1Round_baseChange bo T T' σ p hbc hT hT' hd hd'
      have hpb : (roundTriple bo T' hT' hd').IsBaseChangeOf (roundTriple bo T hT hd) σ
          (eqToHom (congrArg BlowUpSequence.last hR) ≫
            (step1Round bo T hT hd).pullbackLastHom p) :=
        MarkedTriple.isBaseChangeOf_induced_of_eq_seq hR
          (MarkedTriple.isBaseChangeOf_induced_last p hbc (step1Round_isOrderGeSeq bo T hT hd)
            (hbc.isOrderGeSeq_pullback (step1Round_isOrderGeSeq bo T hT hd)))
      have hih := ih (roundTriple bo T hT hd) (roundTriple bo T' hT' hd')
        (eqToHom (congrArg BlowUpSequence.last hR) ≫ (step1Round bo T hT hd).pullbackLastHom p)
        hpb (bmoClass_roundTriple bo T hT hd) (bmoClass_roundTriple bo T' hT' hd')
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo T hT hd) hl))
      exact (congrArg (step1Round bo T' hT' hd').concat (hih.trans (pullback_comp _ _ _))).trans
        (concat_pullback_eqToHom hR _)
    · have hlt : roundOrder T < m := not_le.mp hd
      rw [step1_of_lt bo T hT hlt, step1_of_lt bo T' hT' (hr ▸ hlt), pullback_nil]

/-- **Step 1 commutes with a change of fields** ([Kol07, 34.2] for Step 1): round by round through
the loop, by clause (2) of [Kol07, Theorem 103] on the base-changed round triples. -/
theorem step1_baseChange (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') : (step1 bo T' hT').1 = (step1 bo T hT).1.pullback p :=
  step1_baseChange_aux bo σ (roundOrder T) T T' p hbc hT hT' le_rfl

end Step1

section Step2

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L] {n m : ℕ}
  (bo : ∀ d : ℕ, BOData.{u} n d)

/-- The separating triple `(X, N(I)^m + I^s, E)` of the base-changed data is the base change of
the separating triple: `N(I_L) = p^* N(I)`, the separation order is preserved, and the inverse
image commutes with sums and powers. -/
theorem sepTriple_isBaseChangeOf (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) :
    (sepTriple T').IsBaseChangeOf (sepTriple T) σ p := by
  have hsep : sepOrder T' = sepOrder T := sepOrder_of_isBaseChangeOf T T' hbc
  obtain ⟨⟨hsq, hI, hE⟩, hm⟩ := hbc
  have hN : nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap p :=
    nonmonomialPart_baseChange T.toTriple σ p ⟨hsq, hI, hE⟩
  refine ⟨hsq, ?_, hE⟩
  change sepIdeal T' = (sepIdeal T).comap p
  unfold sepIdeal
  rw [hN, hI, hm, hsep, IdealSheafData.comap_sup, IdealSheafData.comap_pow,
      IdealSheafData.comap_pow]

/-- A round of Step 2 commutes with a change of fields (clause (2) of [Kol07, Theorem 103] with
[Kol07, 34.2], per round): the separation order is preserved and `BO_{n,ms}` commutes on the
base-changed separating triple. -/
theorem step2Round_baseChange (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (hpos : 0 < sepOrder T) (hpos' : 0 < sepOrder T') :
    step2Round bo T' hT' hpos' = (step2Round bo T hT hpos).pullback p := by
  have hr : T'.m * sepOrder T' = T.m * sepOrder T := by
    rw [hbc.2, sepOrder_of_isBaseChangeOf T T' hbc]
  rw [step2Round_eq, step2Round_eq, functor_seq_cast bo hr]
  exact (bo (T.m * sepOrder T)).commutesWithBaseChange k L σ (sepTriple T) (sepTriple T') p
    (sepTriple_isBaseChangeOf T T' σ p hbc) _ _

/-- The induction behind `step2_baseChange`: on a bound `l` for the separation order, following the
recursion of `step2`. -/
theorem step2_baseChange_aux (σ : k →+* L) (l : ℕ) :
    ∀ (T : MarkedTriple k) (T' : MarkedTriple L)
    (p : T'.X.left ⟶ T.X.left), T'.IsBaseChangeOf T σ p →
      ∀ (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T'),
        sepOrder T ≤ l → (step2 bo T' hT').1 = (step2 bo T hT).1.pullback p := by
  induction l with
  | zero =>
    intro T T' p hbc hT hT' hl
    have hr : sepOrder T' = sepOrder T := sepOrder_of_isBaseChangeOf T T' hbc
    have h0 : sepOrder T = 0 := Nat.le_zero.mp hl
    rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo T' hT' (hr.trans h0), pullback_nil]
  | succ l ih =>
    intro T T' p hbc hT hT' hl
    have hr : sepOrder T' = sepOrder T := sepOrder_of_isBaseChangeOf T T' hbc
    by_cases hpos : 0 < sepOrder T
    · have hpos' : 0 < sepOrder T' := hr ▸ hpos
      rw [step2_of_pos bo T hT hpos, step2_of_pos bo T' hT' hpos']
      refine Eq.trans ?_ (pullback_concat (step2Round bo T hT hpos) _ p).symm
      have hR : step2Round bo T' hT' hpos' = (step2Round bo T hT hpos).pullback p :=
        step2Round_baseChange bo T T' σ p hbc hT hT' hpos hpos'
      have hpb : (step2Triple bo T' hT' hpos').IsBaseChangeOf (step2Triple bo T hT hpos) σ
          (eqToHom (congrArg BlowUpSequence.last hR) ≫
            (step2Round bo T hT hpos).pullbackLastHom p) :=
        MarkedTriple.isBaseChangeOf_induced_of_eq_seq hR
          (MarkedTriple.isBaseChangeOf_induced_last p hbc (step2Round_isOrderGeSeq bo T hT hpos)
            (hbc.isOrderGeSeq_pullback (step2Round_isOrderGeSeq bo T hT hpos)))
      have hih := ih (step2Triple bo T hT hpos) (step2Triple bo T' hT' hpos')
        (eqToHom (congrArg BlowUpSequence.last hR) ≫ (step2Round bo T hT hpos).pullbackLastHom p)
        hpb (bmoClass_step2Triple bo T hT hpos) (bmoClass_step2Triple bo T' hT' hpos')
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (sepOrder_step2Triple_lt bo T hT hpos) hl))
      exact (congrArg (step2Round bo T' hT' hpos').concat (hih.trans (pullback_comp _ _ _))).trans
        (concat_pullback_eqToHom hR _)
    · have h0 : sepOrder T = 0 := Nat.eq_zero_of_not_pos hpos
      rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo T' hT' (hr.trans h0), pullback_nil]

/-- **Step 2 commutes with a change of fields** ([Kol07, 34.2] for Step 2): round by round through
the loop, by clause (2) of [Kol07, Theorem 103] on the base-changed separating triples. -/
theorem step2_baseChange (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') : (step2 bo T' hT').1 = (step2 bo T hT).1.pullback p :=
  step2_baseChange_aux bo σ (sepOrder T) T T' p hbc hT hT' le_rfl

end Step2

section Step3

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L] {n m : ℕ}

/-- **The geometric Step 3 of a marked triple commutes with a change of fields** ([Kol07, 34.2] for
Step 3; `realize_pullback_of_isBaseChangeOf` with `refinesAlong_ofDivisorFamily` in its flat
form): Step 3's input family on `X_L` is the refining family up to the exponents, which agree at
the generic points of the components since the projection is flat (it sends generic points to
generic points) and preserves the order at every point (`ord_comap_of_isBaseChangeOf`); the
enumeration `σ'` of the components of `E_L` is Step 3's own. -/
theorem step3Seq_baseChange (T : MarkedTriple k) (T' : MarkedTriple L) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') : step3Seq T' hT' = (step3Seq T hT).pullback p := by
  obtain ⟨⟨hsq, hI, hE⟩, hm⟩ := hbc
  cases T' with
  | mk toT m' =>
  cases toT with
  | mk X' eq' I' hI' E' hE' =>
  obtain ⟨⟨X', _, hom'⟩, ft, sep⟩ := X'
  dsimp only at p hsq hI hE hm
  subst hI hE hm
  have hsm := T.smooth
  have hflat : Flat p := flat_of_isPullback_specMap hsq
  have hbc' : (⟨.ofHom hom' ft sep, eq', T.I.comap p, hI', T.E.comap p, hE'⟩ :
      Triple L).IsBaseChangeOf T.toTriple σ p := ⟨hsq, rfl, rfl⟩
  have hN := Hironaka.BD.noetherianSpace_triple T.toTriple
  have hN' : NoetherianSpace X' := Hironaka.BD.noetherianSpace_triple
    (⟨.ofHom hom' ft sep, eq', T.I.comap p, hI', T.E.comap p, hE'⟩ : Triple L)
  -- the refining family on `X_L`, with Step 3's enumeration of the components
  set σ' : Fin (Nat.card (Components (T.E.comap p))) ≃ Components (T.E.comap p) :=
    @componentsEquiv _ hN' (T.E.comap p) with hσ'
  have hρ := refinesAlong_ofDivisorFamily (f := T.X.left ↘ Spec (.of k)) (h := p)
    (Φ := step3Family T) T.isSnc (step3Family_realizes T) hE' σ'
  have hreal : (ofDivisorFamily (T.E.comap p) (fun y => (step3Family T).exponentAt (p y))
      (labelIso T.E) σ').Realizes (T.E.comap p) (labelIso T.E) :=
    ofDivisorFamily_realizes (T.E.comap p) _ (labelIso T.E) σ' hE'
  have hΦ' : (ofDivisorFamily (T.E.comap p) (fun y => (step3Family T).exponentAt (p y))
      (labelIso T.E) σ').Realizes (T.E.comap p)
      ((labelIso T.E).trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
    refine ⟨fun j => ?_, hreal.disjoint⟩
    change ((T.E.comap p).component j).support =
      ((Finset.range (ofDivisorFamily (T.E.comap p)
        (fun y => (step3Family T).exponentAt (p y)) (labelIso T.E) σ').nextComp).filter
        fun c => (ofDivisorFamily (T.E.comap p) (fun y => (step3Family T).exponentAt (p y))
          (labelIso T.E) σ').label c = (labelIso T.E j : ℕ)).sup
        (ofDivisorFamily (T.E.comap p) (fun y => (step3Family T).exponentAt (p y))
          (labelIso T.E) σ').piece
    exact hreal.support_eq j
  have hn' : ∃ n' ≤ n, SmoothOfRelativeDimension n' hom' := hT'.2.1
  have hV' : (ofDivisorFamily (T.E.comap p) (fun y => (step3Family T).exponentAt (p y))
      (labelIso T.E) σ').IsValid n m :=
    valid_of_realizes _ hom' hE' hreal hT.1 hn'
  have key := realize_pullback_of_isBaseChangeOf (step3Family T) hbc' (step3Family_realizes T)
    (step3Family_isValid T hT) hT.2.1 hT'.2.1 hρ hΦ' hV'
  -- the input family of the base-changed data is the refining family, up to the exponents
  have hagree : ∀ c : Components (T.E.comap p),
      ((T.I.comap p).ord (c.2 : X')).toNat = (step3Family T).exponentAt (p (c.2 : X')) := by
    intro c
    rw [ord_comap_of_isBaseChangeOf hbc']
    exact (exponentAt_step3Family_of_mem_genericPoints T
      (mem_genericPoints_support_of_flat p _ c.2.2)).symm
  have hfam : ofDivisorFamily (T.E.comap p) (fun y => ((T.I.comap p).ord y).toNat)
      (labelIso T.E) σ' = ofDivisorFamily (T.E.comap p)
        (fun y => (step3Family T).exponentAt (p y)) (labelIso T.E) σ' :=
    ofDivisorFamily_congr_of_forall (E := T.E.comap p) _ _ (labelIso T.E) σ' hagree
  change (ofDivisorFamily (T.E.comap p) (fun y => ((T.I.comap p).ord y).toNat) (labelIso T.E)
    σ').realize n m _ = ((step3Family T).realize n m (step3Family_isValid T hT)).pullback p
  rw [← key]
  exact realize_congr_family hfam _ _

end Step3

section Assembly

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}

/-- The tail after Step 2 under a change of fields: the change-of-fields form of
`tailAfterStep2_pullback`, Step 3 by `step3Seq_baseChange` on the marked triples induced after
Step 2 along the last-stage lift. -/
theorem tailAfterStep2_baseChange {L : Type u} [Field L] [CharZero L] (T : MarkedTriple k)
    (T' : MarkedTriple L) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T')
    (τ : {R : BlowUpSequence T.X.left //
      R.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ R.NoEmptyCenters})
    (τ' : {R : BlowUpSequence T'.X.left //
      R.IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E ∧ R.NoEmptyCenters})
    (e : τ'.1 = τ.1.pullback p) :
    tailAfterStep2 T' hT' τ' = (tailAfterStep2 T hT τ).pullback p := by
  obtain ⟨R', hR'⟩ := τ'
  dsimp only at e
  subst e
  dsimp only [tailAfterStep2]
  refine Eq.trans ?_ (pullback_concat _ _ _).symm
  exact congrArg (τ.1.pullback p).concat
    (step3Seq_baseChange _ _ σ _ (MarkedTriple.isBaseChangeOf_induced_last p hbc τ.2.1 hR'.1) _ _)

/-- The tail after Step 1 under a change of fields: the change-of-fields form of
`tailAfterStep1_pullback`. -/
theorem tailAfterStep1_baseChange {L : Type u} [Field L] [CharZero L] (T : MarkedTriple k)
    (T' : MarkedTriple L) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T')
    (S : BlowUpSequence T.X.left)
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters)
    (hS' : (S.pullback p).IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E ∧
      (S.pullback p).NoEmptyCenters) :
    tailAfterStep1 bo T' hT' ⟨S.pullback p, hS'⟩ =
      (tailAfterStep1 bo T hT ⟨S, hS⟩).pullback (S.pullbackLastHom p) := by
  have hpb₁ := MarkedTriple.isBaseChangeOf_induced_last p hbc hS.1 hS'.1
  have h2 := step2_baseChange bo (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback p) hS'.1 (Fin.last _)) σ (S.pullbackLastHom p) hpb₁
    (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))
  dsimp only [tailAfterStep1]
  exact tailAfterStep2_baseChange (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback p) hS'.1 (Fin.last _)) σ (S.pullbackLastHom p) hpb₁
    (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))
    (step2 bo (T.induced S hS.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _)))
    (step2 bo (T'.induced (S.pullback p) hS'.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))) h2

/-- The whole assembly under a change of fields: the change-of-fields form of
`concat_tailAfterStep1_pullback`. -/
theorem concat_tailAfterStep1_baseChange {L : Type u} [Field L] [CharZero L] (T : MarkedTriple k)
    (T' : MarkedTriple L) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    (hT : MarkedTriple.BMOClass n m T) (hT' : MarkedTriple.BMOClass n m T')
    (σ₁ : {S : BlowUpSequence T.X.left //
      S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters})
    (σ₁' : {S : BlowUpSequence T'.X.left //
      S.IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E ∧ S.NoEmptyCenters})
    (e : σ₁'.1 = σ₁.1.pullback p) :
    σ₁'.1.concat (tailAfterStep1 bo T' hT' σ₁') =
      (σ₁.1.concat (tailAfterStep1 bo T hT σ₁)).pullback p := by
  obtain ⟨S', hS'⟩ := σ₁'
  dsimp only at e
  subst e
  refine Eq.trans ?_ (pullback_concat _ _ _).symm
  exact congrArg (σ₁.1.pullback p).concat
    (tailAfterStep1_baseChange bo T T' σ p hbc hT hT' σ₁.1 σ₁.2 hS')

/-- **`BMO_{n,m}` commutes with change of fields** (clause (2) of [Kol07, Theorem 107] with
[Kol07, 34.2]): the field `commutesWithBaseChange` of the order-reduction data on each round, with
the parameters preserved (`roundOrder_of_isBaseChangeOf`, `sepOrder_of_isBaseChangeOf`), and
`step3Seq_baseChange` for Step 3; no blow-up is deleted. -/
theorem commutesWithBaseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) :
    (Hironaka.BMO.functor (k := k) bo m).CommutesWithBaseChange
      (Hironaka.BMO.functor (k := L) bo m) σ := by
  intro T T' p hbc hT hT'
  change bmoSeq bo T' hT' = (bmoSeq bo T hT).pullback p
  rw [bmoSeq_eq_concat_tailAfterStep1, bmoSeq_eq_concat_tailAfterStep1]
  exact concat_tailAfterStep1_baseChange bo T T' σ p hbc hT hT' (step1 bo T hT) (step1 bo T' hT')
    (step1_baseChange bo T T' σ p hbc hT hT')

end Assembly

end Hironaka.BMO
