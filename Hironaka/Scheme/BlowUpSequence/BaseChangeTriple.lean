/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Triple
public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
public import Hironaka.Scheme.BlowUpSequence.BaseChangeParameters
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The base change of a triple and of a smooth blow-up sequence along a field extension

[Kol07, 34.2]: the base change of a triple along `σ : K ↪ L` is the fiber product
`X_{L,σ} := X_K ×_{Spec K} Spec L`, "an `L`-scheme of finite type", with the ideal `I_{L,σ}` and
the divisor `E_{L,σ}` obtained similarly; the change of fields "will hold automatically for all
blow-up sequence functors that we construct". This module provides

* the base change `AlgebraicGeometry.Triple.baseChange T σ : Triple L` of a triple: the fibre
  product `pullback (T.X.left ↘ Spec k) (Spec.map σ)` over `L` through its second projection, with
  `T.I` and `T.E` pulled back along the first. Every field but simple normal crossings is
  base-change stability (the `IsStableUnderBaseChange` instances through `property_of_isPullback`;
  nonvanishing on components by flat pullback); the simple normal crossing field is
  `isSnc_comap_of_isPullback_specMap` of `Hironaka/Scheme/BlowUpSequence/BaseChangeParameters.lean`.
  The construction carries the base-change data `IsBaseChangeOf` through the first projection
  (`isBaseChangeOf_baseChange`); the marked version keeps the mark;
* the base change `S.pullback p` of a smooth blow-up sequence of order `m` (resp. `≥ m`) starting
  with `(X, I, E)` is one starting with `(X_{L,σ}, I_{L,σ}, E_{L,σ})`
  (`Triple.IsBaseChangeOf.isOrderSeq_pullback`,
  `MarkedTriple.IsBaseChangeOf.isOrderGeSeq_pullback`), stage by stage as for a smooth pullback:
  the centers are the inverse images of the centers, the induced families and ideals the inverse
  images of the induced ones (`totalTransformSeq_pullback` for `E`, the transports of
  `Hironaka/Scheme/BlowUpSequence/BaseChangeOrder.lean` for `I`), simple normal crossings and the
  order transport along the stage lifts through the stage squares of
  `Hironaka/Scheme/BlowUpSequence/BaseChange.lean`; and the induced data are the base change of the
  induced data (`induced_isBaseChangeOf`);
* the corresponding statement for the pullback along a smooth morphism
  (`IsPullbackOf.induced_isPullbackOf`) and two transports along an equality of stage indices.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.BlowUpSequence

namespace Hironaka

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-! ### The base change of a triple -/

/-- The base change of a triple over `k` along `σ : k →+* L` [Kol07, 34.2]: the fibre product
`pullback (T.X.left ↘ Spec k) (Spec.map σ)` over `L` through its second projection, with the inverse
images of `T.I` and `T.E` along the first projection. Finite type, quasi-compactness,
separatedness, smoothness and the relative dimension over `L` are base-change stability;
nonvanishing on components is flat pullback; simple normal crossings is
`isSnc_comap_of_isPullback_specMap`. -/
noncomputable def _root_.AlgebraicGeometry.Triple.baseChange [CharZero k] (T : Triple k)
    (σ : k →+* L) : Triple L where
  X := .ofHom (pullback.snd (T.X.left ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom σ)))
    (
      { toLocallyOfFiniteType := property_of_isPullback @LocallyOfFiniteType
          (IsPullback.of_hasPullback _ _).flip inferInstance
        toQuasiCompact := property_of_isPullback @QuasiCompact
          (IsPullback.of_hasPullback _ _).flip inferInstance })
    (
      property_of_isPullback @IsSeparated (IsPullback.of_hasPullback _ _).flip
        inferInstance)
  smoothOfRelativeDimension := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    have := smoothOfRelativeDimension_isStableUnderBaseChange n
    exact ⟨n, property_of_isPullback (@SmoothOfRelativeDimension n)
      (IsPullback.of_hasPullback _ _).flip hn⟩
  I := T.I.comap (pullback.fst _ _)
  isNonzeroEverywhere := by
    have : Flat (pullback.fst (T.X.left ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom σ))) :=
      property_of_isPullback @Flat (IsPullback.of_hasPullback _ _)
        (flat_and_surjective_specMap σ).1
    exact isNonzeroEverywhere_comap_of_flat _ T.isNonzeroEverywhere
  E := T.E.comap (pullback.fst _ _)
  isSnc :=
    isSnc_comap_of_isPullback_specMap (IsPullback.of_hasPullback _ _) T.isSnc

/-- The ambient scheme of the base change is the fibre product. -/
theorem _root_.AlgebraicGeometry.Triple.baseChange_X [CharZero k] (T : Triple k) (σ : k →+* L) :
    (T.baseChange σ).X.left = Limits.pullback (T.X.left ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom σ)) :=
  rfl

/-- The base change of `T` carries the base-change data of `T` (`IsBaseChangeOf`) through the
first projection. -/
theorem _root_.AlgebraicGeometry.Triple.isBaseChangeOf_baseChange [CharZero k] (T : Triple k)
    (σ : k →+* L) : (T.baseChange σ).IsBaseChangeOf T σ (pullback.fst _ _) :=
  ⟨IsPullback.of_hasPullback _ _, rfl, rfl⟩

/-- The base change of a marked triple, the mark unchanged ([Kol07, 34.2]; the pair `(I, m)` is
one item, footnote to [Kol07, Notation 64]). -/
noncomputable def MarkedTriple.baseChange [CharZero k] (T : MarkedTriple k) (σ : k →+* L) :
    MarkedTriple L :=
  { T.toTriple.baseChange σ with m := T.m }

/-- The base change of a marked triple carries the base-change data, with the same mark. -/
theorem MarkedTriple.isBaseChangeOf_baseChange [CharZero k] (T : MarkedTriple k) (σ : k →+* L) :
    (T.baseChange σ).IsBaseChangeOf T σ (pullback.fst _ _) :=
  ⟨Triple.isBaseChangeOf_baseChange T.toTriple σ, rfl⟩

/-! ### The base change of a smooth blow-up sequence of order `m` -/

end Hironaka

namespace AlgebraicGeometry.Triple.IsBaseChangeOf

open Hironaka

variable {k : Type u} [Field k] {L : Type u} [Field L]

open Scheme

variable {T : Triple k} {T' : Triple L} {σ : k →+* L} {p : T'.X.left ⟶ T.X.left}

/-- The base change of a smooth blow-up sequence of order `m` starting with `(X, I, E)` is one
starting with `(X_{L,σ}, I_{L,σ}, E_{L,σ})` [Kol07, 34.2]; the analogue of
`IsOrderSeq.pullback_of_equidim` for the base change: smoothness of the centers by
`isSmooth_pullback`, simple normal crossings by `hasSncWith_comap_of_isPullback_specMap` and the
order by `ordAlongEq_comap_of_isPullback_specMap`, both through the stage squares. -/
theorem isOrderSeq_pullback [CharZero k] (hp : T'.IsBaseChangeOf T σ p)
    {S : BlowUpSequence T.X.left} {m : ℕ} (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) :
    (S.pullback p).IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hflat : Flat p := hp.flat
  rw [hp.2.1, hp.2.2]
  refine ⟨hp.isSmooth_pullback hS.1, ?_⟩
  rintro ⟨j, hj⟩
  have hj' : j < S.length := by rwa [length_pullback] at hj
  have hsm : Smooth (S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := n) hS.1 _
  have hsqj := hp.isPullback_pullbackStageHom S ⟨j, Nat.lt_succ_of_lt hj'⟩
  have hc : (S.pullback p).center ⟨j, hj⟩ =
      (S.center ⟨j, hj'⟩).comap (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk S p j hj'
  have hE : (S.pullback p).totalTransformSeq (T.E.comap p)
        (⟨j, hj⟩ : Fin (S.pullback p).length).castSucc =
      (S.totalTransformSeq T.E ⟨j, Nat.lt_succ_of_lt hj'⟩).comap
        (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    totalTransformSeq_pullback_mk S p T.E j (Nat.lt_succ_of_lt hj')
  have hI : (S.pullback p).weakTransformSeq (T.I.comap p)
        (⟨j, hj⟩ : Fin (S.pullback p).length).castSucc =
      (S.weakTransformSeq T.I ⟨j, Nat.lt_succ_of_lt hj'⟩).comap
        (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    IsOrderSeq.weakTransformSeq_pullback_mk_of_isPullback_specMap hp.1 n hS j
      (Nat.lt_succ_of_lt hj')
  obtain ⟨hsnc, hord⟩ := hS.2 ⟨j, hj'⟩
  have hZ : Smooth ((S.center ⟨j, hj'⟩).subschemeι ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫
      (T.X.left ↘ Spec (.of k))) := hS.1 ⟨j, hj'⟩
  rw [hc, hE, hI]
  exact ⟨hasSncWith_comap_of_isPullback_specMap hsqj hsnc,
    ordAlongEq_comap_of_isPullback_specMap hsqj _ hord⟩

/-- The triple induced at stage `i` of the base-changed sequence ([Kol07, Definition 66, condition
(1)]) carries the base-change data of the triple induced at stage `i` of `S`, through the stage
lift: the stage square, the weak-transform identity
`IsOrderSeq.weakTransformSeq_pullback_of_isPullback_specMap` and `totalTransformSeq_pullback`. -/
theorem induced_isBaseChangeOf [CharZero k] [CharZero L] (hp : T'.IsBaseChangeOf T σ p)
    {S : BlowUpSequence T.X.left} {m : ℕ} (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS' : (S.pullback p).IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m)
    (i : Fin (S.length + 1)) :
    (induced T' (S.pullback p) hS' (S.pullbackStageIdx p i)).IsBaseChangeOf
      (induced T S hS i) σ (S.pullbackStageHom p i) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hflat : Flat p := hp.flat
  refine ⟨hp.isPullback_pullbackStageHom S i, ?_, ?_⟩
  · change (S.pullback p).weakTransformSeq T'.I (S.pullbackStageIdx p i) =
      (S.weakTransformSeq T.I i).comap (S.pullbackStageHom p i)
    rw [hp.2.1]
    exact IsOrderSeq.weakTransformSeq_pullback_of_isPullback_specMap hp.1 n hS i
  · change (S.pullback p).totalTransformSeq T'.E (S.pullbackStageIdx p i) =
      (S.totalTransformSeq T.E i).comap (S.pullbackStageHom p i)
    rw [hp.2.2]
    exact totalTransformSeq_pullback S p T.E i

end AlgebraicGeometry.Triple.IsBaseChangeOf

namespace Hironaka

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-! ### The marked form -/

namespace MarkedTriple.IsBaseChangeOf

open Scheme

variable {T : MarkedTriple k} {T' : MarkedTriple L} {σ : k →+* L} {p : T'.X.left ⟶ T.X.left}

/-- The base change of a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)` is
one starting with `(X_{L,σ}, I_{L,σ}, m, E_{L,σ})` ([Kol07, 34.2]; conditions (2′)–(4′) of
[Kol07, Definition 66]): the `≥ m` condition transports along the flat stage lifts
(`leOrdAlong_comap_of_flat`), simple normal crossings by `hasSncWith_comap_of_isPullback_specMap`,
the marked transforms by `markedTransformSeq_pullback_mk_of_flat`. -/
theorem isOrderGeSeq_pullback [CharZero k] (hp : T'.IsBaseChangeOf T σ p)
    {S : BlowUpSequence T.X.left} (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) :
    (S.pullback p).IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hp0 := hp.1
  have hflat : Flat p := hp0.flat
  rw [hp0.2.1, hp0.2.2, hp.2]
  refine ⟨hp0.isSmooth_pullback hS.1, ?_⟩
  rintro ⟨j, hj⟩
  have hj' : j < S.length := by rwa [length_pullback] at hj
  have hsm : Smooth (S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := n) hS.1 _
  have hsqj := hp0.isPullback_pullbackStageHom S ⟨j, Nat.lt_succ_of_lt hj'⟩
  have hc : (S.pullback p).center ⟨j, hj⟩ =
      (S.center ⟨j, hj'⟩).comap (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk S p j hj'
  have hE : (S.pullback p).totalTransformSeq (T.E.comap p)
        (⟨j, hj⟩ : Fin (S.pullback p).length).castSucc =
      (S.totalTransformSeq T.E ⟨j, Nat.lt_succ_of_lt hj'⟩).comap
        (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    totalTransformSeq_pullback_mk S p T.E j (Nat.lt_succ_of_lt hj')
  have hI : (S.pullback p).markedTransformSeq (T.I.comap p) T.m
        (⟨j, hj⟩ : Fin (S.pullback p).length).castSucc =
      (S.markedTransformSeq T.I T.m ⟨j, Nat.lt_succ_of_lt hj'⟩).comap
        (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    IsOrderGeSeq.markedTransformSeq_pullback_mk_of_flat (T.X.left ↘ Spec (.of k)) n p
      hS j (Nat.lt_succ_of_lt hj')
  obtain ⟨hsnc, hord⟩ := hS.2 ⟨j, hj'⟩
  have : Flat (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    flat_pullbackStageHom S p _
  rw [hc, hE, hI]
  exact ⟨hasSncWith_comap_of_isPullback_specMap hsqj hsnc,
    leOrdAlong_comap_of_flat _ _ hord⟩

/-- The marked triple induced at stage `i` of the base-changed sequence ([Kol07, Definition 66,
condition (1′)]) carries the base-change data, with the same mark, of the one induced at stage `i`
of `S`, through the stage lift. -/
theorem induced_isBaseChangeOf [CharZero k] [CharZero L] (hp : T'.IsBaseChangeOf T σ p)
    {S : BlowUpSequence T.X.left} (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hS' : (S.pullback p).IsOrderGeSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.m T'.E)
    (i : Fin (S.length + 1)) :
    (induced T' (S.pullback p) hS'
        (S.pullbackStageIdx p i)).IsBaseChangeOf
      (induced T S hS i) σ (S.pullbackStageHom p i) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hp0 := hp.1
  have hflat : Flat p := hp0.flat
  refine ⟨⟨hp0.isPullback_pullbackStageHom S i, ?_, ?_⟩, hp.2⟩
  · change (S.pullback p).markedTransformSeq T'.I T'.m (S.pullbackStageIdx p i) =
      (S.markedTransformSeq T.I T.m i).comap (S.pullbackStageHom p i)
    rw [hp0.2.1, hp.2]
    exact IsOrderGeSeq.markedTransformSeq_pullback_of_flat (T.X.left ↘ Spec (.of k)) n
      p hS i
  · change (S.pullback p).totalTransformSeq T'.E (S.pullbackStageIdx p i) =
      (S.totalTransformSeq T.E i).comap (S.pullbackStageHom p i)
    rw [hp0.2.2]
    exact totalTransformSeq_pullback S p T.E i

end MarkedTriple.IsBaseChangeOf

end Hironaka

/-! ### The induced triple of a pulled-back sequence carries the pullback data

The analogues of `induced_isBaseChangeOf` above for the pullback along a smooth morphism, beside
`inducedTriple_pullback` of `Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`. -/

namespace AlgebraicGeometry.Triple

open Hironaka

open Scheme

open AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The triple induced at stage `i` of the pulled-back sequence carries the pullback data of the
triple induced at stage `i`, along the stage lift (`inducedTriple_pullback` as an
`IsPullbackOf`). -/
theorem IsPullbackOf.induced_isPullbackOf [CharZero k] {T T' : Triple k} {h : T'.X.left ⟶ T.X.left}
    [Smooth h] (hp : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left} {m : ℕ}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS' : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (i : Fin (S.length + 1)) :
    (T'.induced (S.pullback h) hS' (S.pullbackStageIdx h i)).IsPullbackOf (T.induced S hS i)
      (S.pullbackStageHom h i) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  have : SmoothOfRelativeDimension n' (h ≫ (T.X.left ↘ Spec (.of k))) := by rw [hp.1]; exact hn'
  refine ⟨?_, ?_, ?_⟩
  · change S.pullbackStageHom h i ≫ (S.stageMap i ≫ (T.X.left ↘ Spec (.of k))) =
      (S.pullback h).stageMap (S.pullbackStageIdx h i) ≫ (T'.X.left ↘ Spec (.of k))
    rw [← Category.assoc, pullbackStageHom_stageMap, Category.assoc, hp.1]
  · change (S.pullback h).weakTransformSeq T'.I (S.pullbackStageIdx h i) =
      (S.weakTransformSeq T.I i).comap (S.pullbackStageHom h i)
    rw [hp.2.1]
    exact IsOrderSeq.weakTransformSeq_pullback_of_equidim (T.X.left ↘ Spec (.of k)) n h n' hS i
  · change (S.pullback h).totalTransformSeq T'.E (S.pullbackStageIdx h i) =
      (S.totalTransformSeq T.E i).comap (S.pullbackStageHom h i)
    rw [hp.2.2]
    exact totalTransformSeq_pullback S h T.E i

/-- Transport of pullback data of an induced triple along an equality of stage indices: the
`eqToHom` of the stage identification is absorbed. -/
theorem isPullbackOf_induced_of_eq_idx [CharZero k] {T' : Triple k} {S' : BlowUpSequence T'.X.left}
    {m : ℕ} {hS' : S'.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m} {i j : Fin (S'.length + 1)}
    (e : i = j) {R : Triple k} {q : S'.stage i ⟶ R.X.left}
    (hq : (T'.induced S' hS' i).IsPullbackOf R q) :
    (T'.induced S' hS' j).IsPullbackOf R (eqToHom (congrArg S'.stage e.symm) ≫ q) := by
  cases e
  exact hq

/-- Transport of base-change data of an induced triple along an equality of stage indices. -/
theorem isBaseChangeOf_induced_of_eq_idx {L : Type u} [Field L] [CharZero L] {T' : Triple L}
    {S' : BlowUpSequence T'.X.left} {m : ℕ}
    {hS' : S'.IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m}
    {i j : Fin (S'.length + 1)} (e : i = j) {R : Triple k} {σ : k →+* L} {q : S'.stage i ⟶ R.X.left}
    (hq : (T'.induced S' hS' i).IsBaseChangeOf R σ q) :
    (T'.induced S' hS' j).IsBaseChangeOf R σ (eqToHom (congrArg S'.stage e.symm) ≫ q) := by
  cases e
  exact hq

end AlgebraicGeometry.Triple
