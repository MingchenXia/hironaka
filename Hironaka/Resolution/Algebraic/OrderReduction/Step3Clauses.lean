/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferent
public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.MaximalContact.PullbackSmooth
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step2EraseEmpty
import Hironaka.Resolution.Algebraic.OrderReduction.Step3Cover
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.BaseChangeParameters
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.IdealSheaf.Derivative.BaseChange
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.Snc.RestrictHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clauses (1)–(2) of order reduction for the globalised functor

Step 3 of the proof of [Kol07, Theorem 103] defines `BO_{n,m}` by descent from a cover and
asserts the clauses of the theorem for it through the locality of the functoriality package
([Kol07, 34]: "the claimed isomorphism is unique, and hence the existence is a local question").
The argument here is one pattern, used four times: a local cover `g : TU → T` (hypothesis (2)(i) of
[Kol07, Theorem 105], `exists_isLocalCover`) is pulled back to the source of the morphism under
study (`Hironaka/Resolution/Algebraic/OrderReduction/Step3Cover.lean`, or its base-change form
`exists_localCover_baseChange` below); both sides of the desired identity pull back along the
surjective open-immersion coproduct `g'` to the local functor's value on the pulled-back cover,
by the descent identity `globalize_seq_pullback` on one side and by the same identity followed by
the corresponding theorem for `maxContactCase` on the other; and a pull-back along a surjective
flat morphism is injective on blow-up sequences (`pullback_injective_of_surjective`). The empty
triple is the degenerate case, where every value is `nil`.

* Clause (1), `functor_maxOrd_lt`: the maximal order at the last stage is read off the cover. The
  last-stage lift is surjective (`surjective_pullbackStageHom`), the weak transform of the
  pull-back is the pull-back of the weak transform (`IsOrderSeq.weakTransformSeq_pullback`), the
  maximal order does not decrease under a surjective pull-back
  (`maxOrd_le_maxOrd_comap_of_surjective`), and on the cover it is `maxOrd_maxContactCase_lt`.
* The first clause of [Kol07, 34.1], `functor_commutesWithSmoothSurjections`: on the pulled-back
  cover the local functor commutes with the smooth surjection (hypothesis (3) of Theorem 105).
* The second clause of [Kol07, 34.1], `functor_commutesWithSmooth`: the deletion of empty blow-ups
  moves through the pull-back along the surjective flat `g'`
  (`eraseEmpty_pullback_of_flat_surjective`), and on the pieces the identity is
  `maxContactCase_eraseEmpty_pullback`, under the indifference `hind` of the boundary-clearing data
  to empty boundary members.
* [Kol07, 34.2], `functor_commutesWithBaseChange`: the cover pulled back along the base-change
  projection is a base-change pair of local triples (`exists_localCover_baseChange`, with the
  transports of a smooth hypersurface of maximal contact along the base-change square,
  `isSmoothDivisor_comap_of_isPullback_specMap` and `isMaximalContact_comap_of_isPullback_specMap`),
  and on the pieces the identity is `maxContactCase_baseChange`.

The clauses are packaged as `BOData n m` in
`Hironaka/Resolution/Algebraic/OrderReduction/Step3Data.lean`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka Scheme
  BlowUpSequence Hironaka.Sequence Hironaka.Snc Scheme.IdealSheafData

namespace Hironaka.BO

section BaseChangeTransports

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L]
  {X Y : Scheme.{u}} {p : Y ⟶ X} {g' : Y ⟶ Spec (.of L)} {f : X ⟶ Spec (.of k)} {σ : k →+* L}

omit [CharZero L] in
/-- The inverse image of a hypersurface of maximal contact under the projection of a base-change
square over a field extension is one for the pulled-back ideal ([Kol07, 34.2]): `MC` is `D^{m-1}`
and the derivative commutes with the square (`derivativeIter_comap_of_isPullback_specMap`). -/
theorem isMaximalContact_comap_of_isPullback_specMap
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) [Smooth f] {I : X.IdealSheafData}
    {m : ℕ} {H : X.IdealSheafData} (hle : IdealSheafData.IsMaximalContact f I m H) :
    IdealSheafData.IsMaximalContact g' (I.comap p) m (H.comap p) := by
  unfold IdealSheafData.IsMaximalContact IdealSheafData.MC at hle ⊢
  rw [IdealSheafData.derivativeIter_comap_of_isPullback_specMap sq (m - 1) I]
  exact IdealSheafData.comap_mono p hle

omit [CharZero L] in
/-- The inverse image of a smooth divisor under the projection of a base-change square over a field
extension is a smooth divisor ([Kol07, 34.2]; `isSnc_comap_of_isPullback_specMap` on the one-member
family, as `isSmoothDivisor_comap_of_smooth` for smooth morphisms). -/
theorem isSmoothDivisor_comap_of_isPullback_specMap
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) [Smooth f] {H : X.IdealSheafData}
    (hH : IsSmoothDivisor H) : IsSmoothDivisor (H.comap p) := by
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk f x
  have hsnc : (((DivisorFamily.empty X).append H).comap p).IsSnc :=
    isSnc_comap_of_isPullback_specMap sq (isSnc_append_empty_of_isSmoothDivisor hreg hH)
  have hg' : Smooth g' := smooth_of_isPullback_specMap sq
  have hregY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk g' y
  exact isSmoothDivisor_of_snc_data (((DivisorFamily.empty X).append H).comap p).component hsnc.1
    (fun y => hsnc.2 y) hregY (toLex (Sum.inr PUnit.unit))

end BaseChangeTransports

section BaseChangeCover

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- The pull-back of a local cover along a base-change projection ([Kol07, 34.2], with the fibre
product of the proof of [Kol07, Theorem 105]): for a local cover `g : TU → T` and a base-change
pair `T'.IsBaseChangeOf T σ p`, the fibre product `W = TU ×_T T'` is a local cover of `T'` along
the second projection and carries the base-change data of `TU` along the first (the two squares
paste to a square over `Spec σ`); `W` lies in the local class by `boClass_isPullbackOf` on the open
leg and the two transports above along the base-change leg. -/
theorem exists_localCover_baseChange {L : Type u} [Field L] [CharZero L] {T TU : Triple k}
    {T' : Triple L} {σ : k →+* L} {p : T'.X.left ⟶ T.X.left} (hbc : T'.IsBaseChangeOf T σ p)
    {g : TU.X.left ⟶ T.X.left}
    (hc : Triple.IsLocalCover openImmersionCoprods (Triple.BOClass n m) (localClass n m) T TU g)
    (hT' : Triple.BOClass n m T') :
    ∃ (W : Triple L) (p' : W.X.left ⟶ TU.X.left) (g' : W.X.left ⟶ T'.X.left), IsPullback p' g' g p ∧
      W.IsBaseChangeOf TU σ p' ∧
      Triple.IsLocalCover openImmersionCoprods (Triple.BOClass n m) (localClass n m) T' W g' := by
  obtain ⟨hT, hTU, hM, hs, hp⟩ := hc
  have sq : IsPullback (Limits.pullback.fst g p) (Limits.pullback.snd g p) g p :=
    IsPullback.of_hasPullback g p
  have hM' : openImmersionCoprods (Limits.pullback.snd g p) :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq hM
  have hs' : Function.Surjective (Limits.pullback.snd g p) := fun y' => by
    obtain ⟨y, hy⟩ := hs (p y')
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := p) y y' hy
    exact ⟨z, hz⟩
  have hsep : IsSeparated (Limits.pullback.snd g p) := openImmersionCoprods_isSeparated hM'
  have het : Etale (Limits.pullback.snd g p) := openImmersionCoprods_etale _ hM'
  let _ : (Limits.pullback g p).Over (Spec (CommRingCat.of L)) :=
    ⟨Limits.pullback.snd g p ≫ (T'.X.left ↘ Spec (CommRingCat.of L))⟩
  have _ : (Limits.pullback.snd g p).IsOver (Spec (CommRingCat.of L)) := ⟨rfl⟩
  have hqc : QuasiCompact g := by
    have : QuasiCompact (g ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
      rw [hp.1]
      infer_instance
    exact QuasiCompact.of_comp g (T.X.left ↘ Spec (CommRingCat.of k))
  have hcpt : CompactSpace T'.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T'.X.left ↘ Spec (CommRingCat.of L))
  have : LocallyOfFiniteType ((Limits.pullback g p) ↘ Spec (CommRingCat.of L)) :=
    inferInstanceAs
      (LocallyOfFiniteType (Limits.pullback.snd g p ≫ (T'.X.left ↘ Spec (CommRingCat.of L))))
  have : IsSeparated ((Limits.pullback g p) ↘ Spec (CommRingCat.of L)) :=
    inferInstanceAs (IsSeparated (Limits.pullback.snd g p ≫ (T'.X.left ↘ Spec (CommRingCat.of L))))
  have : QuasiCompact ((Limits.pullback g p) ↘ Spec (CommRingCat.of L)) := inferInstance
  have hY : ∃ n : ℕ,
      SmoothOfRelativeDimension n ((Limits.pullback g p) ↘ Spec (CommRingCat.of L)) := by
    obtain ⟨n, hn⟩ := T'.smoothOfRelativeDimension
    exact ⟨n, by
      simpa using smoothOfRelativeDimension_comp 0 n (Limits.pullback.snd g p)
        (T'.X.left ↘ Spec (CommRingCat.of L))⟩
  have hW' := Triple.isPullbackOf_pullback T' hY (Limits.pullback.snd g p)
  have hcond : Limits.pullback.fst g p ≫ g = Limits.pullback.snd g p ≫ p :=
    Limits.pullback.condition
  have hsqW : IsPullback (Limits.pullback.fst g p)
      (Limits.pullback.snd g p ≫ (T'.X.left ↘ Spec (CommRingCat.of L)))
      (TU.X.left ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom σ)) := by
    have := sq.paste_vert hbc.1
    rwa [hp.1] at this
  have hWU : (Triple.pullback T' hY (Limits.pullback.snd g p)).IsBaseChangeOf TU σ
      (Limits.pullback.fst g p) := by
    refine ⟨hsqW, ?_, ?_⟩
    · change T'.I.comap (Limits.pullback.snd g p) = TU.I.comap (Limits.pullback.fst g p)
      rw [hp.2.1, hbc.2.1, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        hcond]
    · change T'.E.comap (Limits.pullback.snd g p) = TU.E.comap (Limits.pullback.fst g p)
      rw [hp.2.2, hbc.2.2, ← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, hcond]
  have hL : localClass n m (Triple.pullback T' hY (Limits.pullback.snd g p)) := by
    refine ⟨boClass_isPullbackOf hT' hM' hW', ?_⟩
    obtain ⟨H, hH, hle⟩ := hTU.2
    refine ⟨H.comap (Limits.pullback.fst g p),
      isSmoothDivisor_comap_of_isPullback_specMap hsqW hH, ?_⟩
    have := isMaximalContact_comap_of_isPullback_specMap hsqW hle
    have e2 : TU.I.comap (Limits.pullback.fst g p) = T'.I.comap (Limits.pullback.snd g p) := by
      rw [hp.2.1, hbc.2.1, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        hcond]
    rw [e2] at this
    exact this
  exact ⟨Triple.pullback T' hY (Limits.pullback.snd g p), Limits.pullback.fst g p,
    Limits.pullback.snd g p, sq, hWU, ⟨hT', hL, hM', hs', hW'⟩⟩

end BaseChangeCover

section Clauses

variable {k : Type u} [Field k] [CharZero k] (n m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} n m j)

/-- The descent identity of Step 3 of the proof of [Kol07, Theorem 103] along a local cover:
`g^* BO_{n,m}(X, I, E) = BO_{n,m}(X^*, g^* I, g^{-1} E)` (`globalize_seq_pullback`). -/
theorem functor_seq_pullback_localCover {T T' : Triple k} {g : T'.X.left ⟶ T.X.left}
    (hc : Triple.IsLocalCover openImmersionCoprods (Triple.BOClass n m) (localClass n m) T T' g) :
    ((functor n m bd).seq T hc.1).pullback g = (localFunctor n m bd).seq T' hc.2.1 :=
  OrderSeqAssignment.globalize_seq_pullback (globalizationData_localClass n m)
    (localCoversFibreClosed_localClass n m) (localFunctor n m bd)
    (localFunctor_commutesWithSurjectionsIn n m bd) hc

/-- On an empty scheme every ideal sheaf has maximal order `0`. -/
theorem maxOrd_eq_zero_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (I : X.IdealSheafData) :
    I.maxOrd = 0 :=
  nonpos_iff_eq_zero.mp ((IdealSheafData.maxOrd_le_iff I).mpr fun x => isEmptyElim x)

/-- Clause (1) of [Kol07, Theorem 103] for `BO_{n,m}`: `max-ord I_r < m`, read off a local cover
through the surjective last-stage lift; the clause is local on `X_r`. -/
theorem functor_maxOrd_lt (T : Triple k) (hT : Triple.BOClass n m T) :
    (((functor n m bd).seq T hT).weakTransformSeq T.I (Fin.last _)).maxOrd < (m : ℕ∞) := by
  by_cases hne : Nonempty T.X.left
  · obtain ⟨TU, g, hc⟩ := Triple.exists_isLocalCover (globalizationData_localClass n m) hT
    have hS : ((functor n m bd).seq T hT).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
      (functor n m bd).isOrderSeq T hT
    have hpull : ((functor n m bd).seq T hT).pullback g = (localFunctor n m bd).seq TU hc.2.1 :=
      functor_seq_pullback_localCover n m bd hc
    have het : Etale g := openImmersionCoprods_etale _ hc.2.2.1
    have hfl : Flat g := openImmersionCoprods.flat hc.2.2.1
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    have hwt := IsOrderSeq.weakTransformSeq_pullback (T.X.left ↘ Spec (.of k)) d g (d := 0) hS
      (Fin.last _)
    have hsurj := surjective_pullbackStageHom ((functor n m bd).seq T hT) g hc.2.2.2.1 (Fin.last _)
    have h1 := maxOrd_le_maxOrd_comap_of_surjective _ hsurj
      (((functor n m bd).seq T hT).weakTransformSeq T.I (Fin.last _))
    rw [← hwt, pullbackStageIdx_last] at h1
    refine lt_of_le_of_lt h1 ?_
    rw [← hc.2.2.2.2.2.1, hpull]
    exact maxOrd_maxContactCase_lt TU hc.2.1.1 (Classical.choose_spec hc.2.1.2).1
      (Classical.choose_spec hc.2.1.2).2 bd
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    rw [BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T hT),
      weakTransformSeq_nil]
    exact lt_of_le_of_lt (maxOrd_eq_zero_of_isEmpty T.I).le
      (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hT.1))

/-- Clause (2) of [Kol07, Theorem 103] for `BO_{n,m}`, the first clause of [Kol07, 34.1]:
`BO_{n,m}` commutes with smooth surjections. Both sides pull back along the pulled-back cover to
the local functor's value on the pulled-back local triple (hypothesis (3) of
[Kol07, Theorem 105]), and a surjective flat pull-back is injective on sequences. -/
theorem functor_commutesWithSmoothSurjections :
    (functor (k := k) n m bd).CommutesWithSmoothSurjections := by
  intro T T' h _ hs hpb hT hT'
  by_cases hne : Nonempty T.X.left
  · obtain ⟨TU, g, hc⟩ := Triple.exists_isLocalCover (globalizationData_localClass n m) hT
    obtain ⟨W, h', g', sq, hWU, hc', hsm', hsurj⟩ := exists_localCover_pullback hpb hc hT'
    have hs' : Function.Surjective h' := hsurj hs
    have hfl : Flat g' := openImmersionCoprods.flat hc'.2.2.1
    apply pullback_injective_of_surjective g' hc'.2.2.2.1
    have e1 : ((functor n m bd).seq T' hT').pullback g' = (localFunctor n m bd).seq W hc'.2.1 :=
      functor_seq_pullback_localCover n m bd hc'
    have e2 : ((functor n m bd).seq T hT).pullback g = (localFunctor n m bd).seq TU hc.2.1 :=
      functor_seq_pullback_localCover n m bd hc
    have e3 : (((functor n m bd).seq T hT).pullback h).pullback g' =
        (((functor n m bd).seq T hT).pullback g).pullback h' := by
      rw [← pullback_comp, ← pullback_comp, sq.w]
    rw [e1, e3, e2]
    exact localFunctor_commutesWithSmoothSurjections n m bd TU W h' hs' hWU hc.2.1 hc'.2.1
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    have : IsEmpty T'.X.left := ⟨fun x => IsEmpty.false (h x)⟩
    rw [BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T hT),
      BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T' hT'),
      pullback_nil]

/-- Clause (2) of [Kol07, Theorem 103] for `BO_{n,m}`, both clauses of [Kol07, 34.1]: `BO_{n,m}`
commutes with smooth morphisms. The second clause (an arbitrary smooth `h`, empty blow-ups
deleted) holds under the indifference `hind` of the boundary-clearing data to empty boundary
members: the deletion moves through the pull-back along the surjective flat `g'`, and on the pieces
the identity is `maxContactCase_eraseEmpty_pullback`. -/
theorem functor_commutesWithSmooth (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m)) :
    (functor (k := k) n m bd).CommutesWithSmooth := by
  refine ⟨functor_commutesWithSmoothSurjections n m bd, ?_⟩
  intro T T' h _ hpb hT hT'
  by_cases hne : Nonempty T.X.left
  · obtain ⟨TU, g, hc⟩ := Triple.exists_isLocalCover (globalizationData_localClass n m) hT
    obtain ⟨W, h', g', sq, hWU, hc', hsm', -⟩ := exists_localCover_pullback hpb hc hT'
    have hfl : Flat g' := openImmersionCoprods.flat hc'.2.2.1
    have hsg' : Function.Surjective g' := hc'.2.2.2.1
    apply pullback_injective_of_surjective g' hsg'
    have e1 : ((functor n m bd).seq T' hT').pullback g' = (localFunctor n m bd).seq W hc'.2.1 :=
      functor_seq_pullback_localCover n m bd hc'
    have e2 : ((functor n m bd).seq T hT).pullback g = (localFunctor n m bd).seq TU hc.2.1 :=
      functor_seq_pullback_localCover n m bd hc
    have e3 : (((functor n m bd).seq T hT).pullback h).pullback g' =
        (((functor n m bd).seq T hT).pullback g).pullback h' := by
      rw [← pullback_comp, ← pullback_comp, sq.w]
    rw [e1, ← eraseEmpty_pullback_of_flat_surjective _ g' hsg', e3, e2]
    obtain ⟨d, hd⟩ := TU.smoothOfRelativeDimension
    have hH' : IsSmoothDivisor ((Classical.choose hc.2.1.2).comap h') :=
      isSmoothDivisor_comap_of_smooth (TU.X.left ↘ Spec (.of k)) h'
        (Classical.choose_spec hc.2.1.2).1
    have hle' : IdealSheafData.IsMaximalContact (W.X.left ↘ Spec (.of k)) W.I m
        ((Classical.choose hc.2.1.2).comap h') := by
      have := IdealSheafData.isMaximalContact_comap_of_smooth (TU.X.left ↘ Spec (.of k)) d h'
        (Classical.choose_spec hc.2.1.2).2
      rwa [hWU.1, ← hWU.2.1] at this
    rw [localFunctor_seq n m bd W hc'.2.1 hH' hle']
    exact maxContactCase_eraseEmpty_pullback TU hc.2.1.1 (Classical.choose_spec hc.2.1.2).1
      (Classical.choose_spec hc.2.1.2).2 bd hind hc'.2.1.1 h' hWU hH' hle'
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    have : IsEmpty T'.X.left := ⟨fun x => IsEmpty.false (h x)⟩
    rw [BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T hT),
      BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T' hT'),
      pullback_nil, eraseEmpty_nil]

/-- Clause (2) of [Kol07, Theorem 103] for `BO_{n,m}`, [Kol07, 34.2]: `BO_{n,m}` commutes with
change of fields. The cover is pulled back along the base-change projection
(`exists_localCover_baseChange`), the identity on the pieces is `maxContactCase_baseChange`, and
the pull-back along the surjective open-immersion coproduct is injective. -/
theorem functor_commutesWithBaseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) :
    (functor (k := k) n m bd).CommutesWithBaseChange (functor (k := L) n m bd) σ := by
  intro T T' p hbc hT hT'
  by_cases hne : Nonempty T.X.left
  · obtain ⟨TU, g, hc⟩ := Triple.exists_isLocalCover (globalizationData_localClass n m) hT
    obtain ⟨W, p', g', sq, hWU, hc'⟩ := exists_localCover_baseChange hbc hc hT'
    have hfl : Flat g' := openImmersionCoprods.flat hc'.2.2.1
    apply pullback_injective_of_surjective g' hc'.2.2.2.1
    have e1 : ((functor n m bd).seq T' hT').pullback g' = (localFunctor n m bd).seq W hc'.2.1 :=
      functor_seq_pullback_localCover n m bd hc'
    have e2 : ((functor n m bd).seq T hT).pullback g = (localFunctor n m bd).seq TU hc.2.1 :=
      functor_seq_pullback_localCover n m bd hc
    have e3 : (((functor n m bd).seq T hT).pullback p).pullback g' =
        (((functor n m bd).seq T hT).pullback g).pullback p' := by
      rw [← pullback_comp, ← pullback_comp, sq.w]
    rw [e1, e3, e2]
    have hH' : IsSmoothDivisor ((Classical.choose hc.2.1.2).comap p') :=
      isSmoothDivisor_comap_of_isPullback_specMap hWU.1 (Classical.choose_spec hc.2.1.2).1
    have hle' : IdealSheafData.IsMaximalContact (W.X.left ↘ Spec (.of L)) W.I m
        ((Classical.choose hc.2.1.2).comap p') := by
      have := isMaximalContact_comap_of_isPullback_specMap hWU.1 (Classical.choose_spec hc.2.1.2).2
      rwa [← hWU.2.1] at this
    rw [localFunctor_seq n m bd W hc'.2.1 hH' hle']
    exact maxContactCase_baseChange TU hc.2.1.1 (Classical.choose_spec hc.2.1.2).1
      (Classical.choose_spec hc.2.1.2).2 bd hc'.2.1.1 σ p' hWU hH' hle'
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    have : IsEmpty T'.X.left := ⟨fun x => IsEmpty.false (p x)⟩
    rw [BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T hT),
      BlowUpSequence.eq_nil_of_noEmptyCenters _ ((functor n m bd).noEmptyCenters T' hT'),
      pullback_nil]

end Clauses

end Hironaka.BO
