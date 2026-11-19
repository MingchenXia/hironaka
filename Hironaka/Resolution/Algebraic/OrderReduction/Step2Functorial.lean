/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalFamilyPullback
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.3 of order reduction: functoriality of Step 2 and of the maximal-contact case

[Kol07, 104, Step 2.3] ("as we noted in (34), the functoriality package is local") and clause (2)
of [Kol07, Theorem 103]: `BO_{n,m}` commutes with smooth morphisms ([Kol07, 34.1]) and with
change of fields ([Kol07, 34.2]). For the maximal-contact case `BO^H_{n,m}` (`maxContactCase`,
`Hironaka/Resolution/Algebraic/OrderReduction/Step22RestrictToHypersurface.lean`) the package is
assembled from the functoriality of Step 2.1
(`Hironaka/Resolution/Algebraic/OrderReduction/Step21Functorial.lean`) and the fields of the
boundary-clearing data of [Kol07, Lemma 102] at the mark on the tuned Step 2.2 triple:

* the Step 2.2 triple of the pulled-back data, built on the pulled-back Step 2.1 sequence, is the
  pull-back of the Step 2.2 triple along the last-stage lift (`isPullbackOf_step22TripleOfSeq`,
  `isBaseChangeOf_step22TripleOfSeq`): the induced triples by `isPullbackOf_induced_last`, the
  boundary `F_r + H_r` by `exceptionalFamily_pullback`, `strictTransformSeq_pullback` at the last
  stage and `comap_append`;
* hence Step 2.2 commutes (`step22Seq_pullback_of_surjective_aux`, `step22Seq_baseChange_aux`): at
  the mark, which is preserved by a smooth surjection (`maxOrd_comap_le_of_smooth`,
  `maxOrd_le_maxOrd_comap_of_surjective`) and by a change of fields
  (`maxOrd_comap_of_isPullback_specMap`), by Lemma 102 at `s(m)` on the tuned triples, whose
  pull-back relation is `isPullbackOf_tuned`, resp. `isBaseChangeOf_tuned`; below the mark both
  sides are empty;
* Step 2 is the concatenation (`step2Seq_pullback_of_surjective`, `step2Seq_baseChange`; the Step
  2.1 sequence of the pulled-back data is rewritten through the generalised `step22TripleOfSeq`),
  and `BO^H_{n,m}` follows through the case split of `maxContactCase` on the mark
  (`maxContactCase_pullback_of_surjective`, `maxContactCase_baseChange`).

The second clause of [Kol07, 34.1], for an arbitrary smooth morphism with the empty blow-ups
deleted, is `maxContactCase_eraseEmpty_pullback` in
`Hironaka/Resolution/Algebraic/OrderReduction/Step2EraseEmpty.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.BO

section TripleOf

variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

/-- The Step 2.2 triple of `H` built from an arbitrary sequence `S₁` of order `m`, given with its
order proof and the normal-crossings proof of its boundary `F_r + H_r`; `step22Triple` is this at
the Step 2.1 sequence. -/
noncomputable abbrev step22TripleOfSeq (T : Triple k) (S₁ : BlowUpSequence T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    Triple k :=
  { T.induced S₁ hS₁ (Fin.last _) with
    E := (S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))
    isSnc := hsnc }

/-- The Step 2.2 triple of `h⁻¹H` on the pulled-back Step 2.1 sequence is the pull-back of the
Step 2.2 triple of `H` along the last-stage lift. -/
theorem isPullbackOf_step22TripleOfSeq {T T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS₁' : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc' : (((S₁.pullback h).exceptionalFamily T'.E).append
      ((S₁.pullback h).strictTransformSeq (H.comap h) (Fin.last _))).IsSnc) :
    (step22TripleOfSeq T' (S₁.pullback h) hS₁' hsnc').IsPullbackOf (step22TripleOfSeq T S₁ hS₁ hsnc)
      (S₁.pullbackLastHom h) := by
  have base := isPullbackOf_induced_last h hpb hS₁ hS₁'
  refine ⟨base.1, base.2.1, ?_⟩
  have e2 : (S₁.pullback h).exceptionalFamily T'.E =
      (S₁.exceptionalFamily T.E).comap (S₁.pullbackLastHom h) :=
    (congrArg (fun E => (S₁.pullback h).exceptionalFamily E =
      (S₁.exceptionalFamily T.E).comap (S₁.pullbackLastHom h)) hpb.2.2).mpr
      (exceptionalFamily_pullback S₁ h T.E)
  exact (congrArg₂ DivisorFamily.append e2 (strictTransformSeq_pullback_last S₁ h H)).trans
    (DivisorFamily.comap_append _ _ _).symm

/-- The Step 2.2 triple of `p⁻¹H` on the base-changed Step 2.1 sequence is the base change of the
Step 2.2 triple of `H` along the last-stage lift ([Kol07, 34.2]). -/
theorem isBaseChangeOf_step22TripleOfSeq {L : Type u} [Field L] [CharZero L] {T : Triple k}
    {T' : Triple L} (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    {S₁ : BlowUpSequence T.X.left} (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS₁' : (S₁.pullback p).IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc' : (((S₁.pullback p).exceptionalFamily T'.E).append
      ((S₁.pullback p).strictTransformSeq (H.comap p) (Fin.last _))).IsSnc) :
    (step22TripleOfSeq T' (S₁.pullback p) hS₁' hsnc').IsBaseChangeOf
      (step22TripleOfSeq T S₁ hS₁ hsnc) σ (S₁.pullbackLastHom p) := by
  have hflat : Flat p := hbc.flat
  have base := isBaseChangeOf_induced_last σ p hbc hS₁ hS₁'
  refine ⟨base.1, base.2.1, ?_⟩
  have e2 : (S₁.pullback p).exceptionalFamily T'.E =
      (S₁.exceptionalFamily T.E).comap (S₁.pullbackLastHom p) :=
    (congrArg (fun E => (S₁.pullback p).exceptionalFamily E =
      (S₁.exceptionalFamily T.E).comap (S₁.pullbackLastHom p)) hbc.2.2).mpr
      (exceptionalFamily_pullback S₁ p T.E)
  exact (congrArg₂ DivisorFamily.append e2 (strictTransformSeq_pullback_last S₁ p H)).trans
    (DivisorFamily.comap_append _ _ _).symm

end TripleOf

section Step22Seq

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bd : ∀ m j : ℕ, BDData.{u} n m j)
  (hm : 1 ≤ m)

/-- Step 2.2 (the boundary-clearing functor of [Kol07, Lemma 102] at the mark through the
re-tuning) commutes with a smooth surjection between Step 2.2 triples related by the last-stage
lift. -/
theorem step22Seq_pullback_of_surjective_aux {T T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS₁' : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc' : (((S₁.pullback h).exceptionalFamily T'.E).append
      ((S₁.pullback h).strictTransformSeq (H.comap h) (Fin.last _))).IsSnc) (j : ℕ)
    (hT₂ : Triple.BDClass n m j (step22TripleOfSeq T S₁ hS₁ hsnc))
    (hT₂' : Triple.BDClass n m j (step22TripleOfSeq T' (S₁.pullback h) hS₁' hsnc')) :
    (step22Functor bd m j hm).seq (step22TripleOfSeq T' (S₁.pullback h) hS₁' hsnc') hT₂' =
      ((step22Functor bd m j hm).seq (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂).pullback
        (S₁.pullbackLastHom h) := by
  have hpb₂ := isPullbackOf_step22TripleOfSeq h hpb hS₁ hS₁' hsnc hsnc'
  have hq0 : Smooth (S₁.pullbackLastHom h) := smooth_pullbackLastHom S₁ h
  have hq : @Smooth ((step22TripleOfSeq T' (S₁.pullback h) hS₁' hsnc').tuned m hm).X.left
      ((step22TripleOfSeq T S₁ hS₁ hsnc).tuned m hm).X.left (S₁.pullbackLastHom h) :=
    smooth_pullbackLastHom S₁ h
  have hqs := surjective_pullbackLastHom S₁ h hs
  have hmax_eq : (step22TripleOfSeq T' (S₁.pullback h) hS₁' hsnc').I.maxOrd =
      (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd := by
    rw [hpb₂.2.1]
    exact le_antisymm (maxOrd_comap_le_of_smooth (S₁.pullbackLastHom h) _)
      (maxOrd_le_maxOrd_comap_of_surjective (S₁.pullbackLastHom h) hqs _)
  by_cases h₂ : (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd = m
  · rw [step22Functor_seq_of_maxOrd_eq bd m j hm _ hT₂ h₂,
      step22Functor_seq_of_maxOrd_eq bd m j hm _ hT₂' (hmax_eq.trans h₂)]
    exact ((bd (tuningParam m) j).commutesWithSmooth k).1
      ((step22TripleOfSeq T S₁ hS₁ hsnc).tuned m hm)
      ((step22TripleOfSeq T' (S₁.pullback h) hS₁' hsnc').tuned m hm) (S₁.pullbackLastHom h) hqs
      (isPullbackOf_tuned hpb₂ m hm) _ _
  · have hlt : (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd < m := lt_of_le_of_ne hT₂.2.1 h₂
    rw [step22Functor_seq_of_maxOrd_lt bd m j hm _ hT₂ hlt,
      step22Functor_seq_of_maxOrd_lt bd m j hm _ hT₂' (hmax_eq ▸ hlt)]
    exact (pullback_nil _).symm

/-- Step 2.2 commutes with a change of fields between Step 2.2 triples related by the last-stage
lift ([Kol07, 34.2]). -/
theorem step22Seq_baseChange_aux {L : Type u} [Field L] [CharZero L] {T : Triple k} {T' : Triple L}
    (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS₁' : (S₁.pullback p).IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc' : (((S₁.pullback p).exceptionalFamily T'.E).append
      ((S₁.pullback p).strictTransformSeq (H.comap p) (Fin.last _))).IsSnc) (j : ℕ)
    (hT₂ : Triple.BDClass n m j (step22TripleOfSeq T S₁ hS₁ hsnc))
    (hT₂' : Triple.BDClass n m j (step22TripleOfSeq T' (S₁.pullback p) hS₁' hsnc')) :
    (step22Functor bd m j hm).seq (step22TripleOfSeq T' (S₁.pullback p) hS₁' hsnc') hT₂' =
      ((step22Functor bd m j hm).seq (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂).pullback
        (S₁.pullbackLastHom p) := by
  have hbc₂ := isBaseChangeOf_step22TripleOfSeq σ p hbc hS₁ hS₁' hsnc hsnc'
  obtain ⟨n₁, hn₁⟩ := (step22TripleOfSeq T S₁ hS₁ hsnc).smoothOfRelativeDimension
  obtain ⟨n₂, hn₂⟩ := (step22TripleOfSeq T' (S₁.pullback p) hS₁' hsnc').smoothOfRelativeDimension
  have hmax_eq : (step22TripleOfSeq T' (S₁.pullback p) hS₁' hsnc').I.maxOrd =
      (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd := by
    rw [hbc₂.2.1]
    exact maxOrd_comap_of_isPullback_specMap hbc₂.1 n₁ n₂ _
  by_cases h₂ : (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd = m
  · rw [step22Functor_seq_of_maxOrd_eq bd m j hm _ hT₂ h₂,
      step22Functor_seq_of_maxOrd_eq bd m j hm _ hT₂' (hmax_eq.trans h₂)]
    exact (bd (tuningParam m) j).commutesWithBaseChange k L σ
      ((step22TripleOfSeq T S₁ hS₁ hsnc).tuned m hm)
      ((step22TripleOfSeq T' (S₁.pullback p) hS₁' hsnc').tuned m hm) (S₁.pullbackLastHom p)
      (isBaseChangeOf_tuned hbc₂ m hm) _ _
  · have hlt : (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd < m := lt_of_le_of_ne hT₂.2.1 h₂
    rw [step22Functor_seq_of_maxOrd_lt bd m j hm _ hT₂ hlt,
      step22Functor_seq_of_maxOrd_lt bd m j hm _ hT₂' (hmax_eq ▸ hlt)]
    exact (pullback_nil _).symm

end Step22Seq

section Step2

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)
  {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- Step 2 on the pulled-back data, generalised over its Step 2.1 sequence `S₁'` with
`S₁' = S₁.pullback h`: it is the pull-back of Step 2. -/
theorem step2Seq_pullback_of_surjective_aux {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hpb : T'.IsPullbackOf T h)
    (S₁' : BlowUpSequence T'.X.left) (hS₁' : S₁'.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (e₁ : S₁' = (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h)
    (hsnc' : ((S₁'.exceptionalFamily T'.E).append
      (S₁'.strictTransformSeq (H.comap h) (Fin.last _))).IsSnc) (j' : ℕ)
    (hj' : j' = Fintype.card
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι)
    (hT₂' : Triple.BDClass n m j' (step22TripleOfSeq T' S₁' hS₁' hsnc')) :
    S₁'.concat ((step22Functor bd m j' hm).seq (step22TripleOfSeq T' S₁' hS₁' hsnc') hT₂') =
      (step2Seq T hn hmax bd hm hH hle).pullback h := by
  subst e₁
  subst hj'
  refine Eq.trans ?_ (pullback_concat _ _ h).symm
  exact congrArg _ (step22Seq_pullback_of_surjective_aux bd hm h hs hpb
    (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) hS₁'
    (step22Triple T hn hmax bd hm hH hle).isSnc hsnc' _
    (bdClass_step22Triple T hn hmax bd hm hH hle) hT₂')

/-- Step 2 commutes with smooth surjections ([Kol07, 104, Step 2.3] with the first clause of
[Kol07, 34.1]). -/
theorem step2Seq_pullback_of_surjective {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hH' : IsSmoothDivisor (H.comap h))
    (hle' : IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of k)) T'.I m (H.comap h))
    (hs : Function.Surjective h) (hpb : T'.IsPullbackOf T h) :
    step2Seq T' hn' hmax' bd hm hH' hle' = (step2Seq T hn hmax bd hm hH hle).pullback h := by
  have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hpb.2.2))
  have e₁ : (step21Seq T' hn' hmax' (bd m) (Fintype.card T'.E.ι)).1 =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h := by
    rw [hcard]
    exact step21Seq_pullback_of_surjective T hn hmax (bd m) hn' hmax' h hs hpb _
  have hj1 : ∀ S' : BlowUpSequence T'.X.left,
      S' = (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h →
      Fintype.card (S'.exceptionalFamily T'.E).ι = Fintype.card
        (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h).exceptionalFamily
          T'.E).ι := by
    rintro S' rfl
    rfl
  have hj2 : Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
      h).exceptionalFamily T'.E).ι = Fintype.card
      (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h).exceptionalFamily
        (T.E.comap h)).ι := by
    rw [hpb.2.2]
  have hj3 : Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
      h).exceptionalFamily (T.E.comap h)).ι = Fintype.card
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι (exceptionalFamily_pullback _ h T.E)))
  have hj' := (hj1 _ e₁).trans (hj2.trans hj3)
  exact step2Seq_pullback_of_surjective_aux T hn hmax bd hm hH hle h hs hpb _
    (isOrderSeq_step21Seq T' hn' hmax' (bd m) (Fintype.card T'.E.ι)) e₁
    (step22Triple T' hn' hmax' bd hm hH' hle').isSnc _ hj'
    (bdClass_step22Triple T' hn' hmax' bd hm hH' hle')

/-- Step 2 on the base-changed data, generalised over its Step 2.1 sequence. -/
theorem step2Seq_baseChange_aux {L : Type u} [Field L] [CharZero L] {T' : Triple L}
    (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    (S₁' : BlowUpSequence T'.X.left) (hS₁' : S₁'.IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m)
    (e₁ : S₁' = (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback p)
    (hsnc' : ((S₁'.exceptionalFamily T'.E).append
      (S₁'.strictTransformSeq (H.comap p) (Fin.last _))).IsSnc) (j' : ℕ)
    (hj' : j' = Fintype.card
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι)
    (hT₂' : Triple.BDClass n m j' (step22TripleOfSeq T' S₁' hS₁' hsnc')) :
    S₁'.concat ((step22Functor bd m j' hm).seq (step22TripleOfSeq T' S₁' hS₁' hsnc') hT₂') =
      (step2Seq T hn hmax bd hm hH hle).pullback p := by
  subst e₁
  subst hj'
  refine Eq.trans ?_ (pullback_concat _ _ p).symm
  exact congrArg _ (step22Seq_baseChange_aux bd hm σ p hbc
    (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) hS₁'
    (step22Triple T hn hmax bd hm hH hle).isSnc hsnc' _
    (bdClass_step22Triple T hn hmax bd hm hH hle) hT₂')

/-- Step 2 commutes with change of fields ([Kol07, 34.2]). -/
theorem step2Seq_baseChange {L : Type u} [Field L] [CharZero L] {T' : Triple L}
    (hn' : T'.HasDimLE n) (hmax' : T'.I.maxOrd ≤ m) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left)
    (hbc : T'.IsBaseChangeOf T σ p) (hH' : IsSmoothDivisor (H.comap p))
    (hle' : IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of L)) T'.I m (H.comap p)) :
    step2Seq T' hn' hmax' bd hm hH' hle' = (step2Seq T hn hmax bd hm hH hle).pullback p := by
  have hflat : Flat p := hbc.flat
  have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hbc.2.2))
  have e₁ : (step21Seq T' hn' hmax' (bd m) (Fintype.card T'.E.ι)).1 =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback p := by
    rw [hcard]
    exact step21Seq_baseChange T hn hmax (bd m) hn' hmax' σ p hbc _
  have hj1 : ∀ S' : BlowUpSequence T'.X.left,
      S' = (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback p →
      Fintype.card (S'.exceptionalFamily T'.E).ι = Fintype.card
        (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback p).exceptionalFamily
          T'.E).ι := by
    rintro S' rfl
    rfl
  have hj2 : Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
      p).exceptionalFamily T'.E).ι = Fintype.card
      (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback p).exceptionalFamily
        (T.E.comap p)).ι := by
    rw [hbc.2.2]
  have hj3 : Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
      p).exceptionalFamily (T.E.comap p)).ι = Fintype.card
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι (exceptionalFamily_pullback _ p T.E)))
  have hj' := (hj1 _ e₁).trans (hj2.trans hj3)
  exact step2Seq_baseChange_aux T hn hmax bd hm hH hle σ p hbc _
    (isOrderSeq_step21Seq T' hn' hmax' (bd m) (Fintype.card T'.E.ι)) e₁
    (step22Triple T' hn' hmax' bd hm hH' hle').isSnc _ hj'
    (bdClass_step22Triple T' hn' hmax' bd hm hH' hle')

end Step2

section Assembly

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hT : Triple.BOClass n m T)
  {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H) (bd : ∀ m j : ℕ,
      BDData.{u} n m j)

/-- **The maximal-contact case of order reduction commutes with smooth surjections** (clause (2)
of [Kol07, Theorem 103] with the first clause of [Kol07, 34.1]). -/
theorem maxContactCase_pullback_of_surjective {T' : Triple k} (hT' : Triple.BOClass n m T')
    (h : T'.X.left ⟶ T.X.left) [Smooth h] (hs : Function.Surjective h) (hpb : T'.IsPullbackOf T h)
    (hH' : IsSmoothDivisor (H.comap h))
    (hle' : IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of k)) T'.I m (H.comap h)) :
    maxContactCase T' hT' hH' hle' bd = (maxContactCase T hT hH hle bd).pullback h := by
  have hmax_eq : T'.I.maxOrd = T.I.maxOrd := by
    rw [hpb.2.1]
    exact le_antisymm (maxOrd_comap_le_of_smooth h _) (maxOrd_le_maxOrd_comap_of_surjective h hs _)
  by_cases h₁ : T.I.maxOrd = m
  · rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h₁,
      maxContactCase_of_maxOrd_eq T' hT' hH' hle' bd (hmax_eq.trans h₁)]
    exact step2Seq_pullback_of_surjective (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
      (le_of_eq (maxOrd_tuned h₁ hT.1)) bd (one_le_tuningParam m) hH
      (retune_keeps_maxContact h₁ hT.1 hle) (T' := T'.tuned m hT'.1)
      (hasDimLE_tuned hT'.2.1 m hT'.1) (le_of_eq (maxOrd_tuned (hmax_eq.trans h₁) hT'.1)) h hH'
      (retune_keeps_maxContact (hmax_eq.trans h₁) hT'.1 hle') hs (isPullbackOf_tuned hpb m hT.1)
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.2 h₁
    rw [maxContactCase_of_maxOrd_lt T hT hH hle bd hlt,
      maxContactCase_of_maxOrd_lt T' hT' hH' hle' bd (hmax_eq ▸ hlt)]
    exact (pullback_nil _).symm

/-- **The maximal-contact case of order reduction commutes with change of fields** (clause (2) of
[Kol07, Theorem 103] with [Kol07, 34.2]). -/
theorem maxContactCase_baseChange {L : Type u} [Field L] [CharZero L] {T' : Triple L}
    (hT' : Triple.BOClass n m T') (σ : k →+* L) (p : T'.X.left ⟶ T.X.left)
    (hbc : T'.IsBaseChangeOf T σ p)
    (hH' : IsSmoothDivisor (H.comap p))
    (hle' : IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of L)) T'.I m (H.comap p)) :
    maxContactCase T' hT' hH' hle' bd = (maxContactCase T hT hH hle bd).pullback p := by
  obtain ⟨n₁, hn₁⟩ := T.smoothOfRelativeDimension
  obtain ⟨n₂, hn₂⟩ := T'.smoothOfRelativeDimension
  have hmax_eq : T'.I.maxOrd = T.I.maxOrd := by
    rw [hbc.2.1]
    exact maxOrd_comap_of_isPullback_specMap hbc.1 n₁ n₂ _
  by_cases h₁ : T.I.maxOrd = m
  · rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h₁,
      maxContactCase_of_maxOrd_eq T' hT' hH' hle' bd (hmax_eq.trans h₁)]
    exact step2Seq_baseChange (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
      (le_of_eq (maxOrd_tuned h₁ hT.1)) bd (one_le_tuningParam m) hH
      (retune_keeps_maxContact h₁ hT.1 hle) (T' := T'.tuned m hT'.1)
      (hasDimLE_tuned hT'.2.1 m hT'.1) (le_of_eq (maxOrd_tuned (hmax_eq.trans h₁) hT'.1)) σ p
      (isBaseChangeOf_tuned hbc m hT.1) hH' (retune_keeps_maxContact (hmax_eq.trans h₁) hT'.1 hle')
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.2 h₁
    rw [maxContactCase_of_maxOrd_lt T hT hH hle bd hlt,
      maxContactCase_of_maxOrd_lt T' hT' hH' hle' bd (hmax_eq ▸ hlt)]
    exact (pullback_nil _).symm

end Assembly

end Hironaka.BO
