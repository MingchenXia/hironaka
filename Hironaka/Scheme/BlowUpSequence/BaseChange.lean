/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Base change of a blow-up sequence along a field extension

The change of fields of [Kol07, 34.2]: for a field extension `σ : K ↪ L`, the `L`-scheme
`X_{L,σ} := X_K ×_{Spec K} Spec L` and the base-changed sequence `(π_i)_{L,σ}` with centers
`(Z_i)_{L,σ}`. The base-change data are the predicate `Triple.IsBaseChangeOf T' T σ p` of
`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean` (the square of `p : T'.X.left ⟶ T.X.left`,
the structure morphisms and `Spec σ` is cartesian, and `I`, `E` pull back), and the base-changed
sequence is the pullback `S.pullback p` of `Hironaka/Scheme/BlowUpSequence/Pullback.lean`. This
module proves the routine transports:

* `flat_and_surjective_specMap`: `Spec σ` is flat and surjective, `σ` being faithfully flat (`L`
  is a nonzero free `k`-module; `flat_and_surjective_SpecMap_iff`);
* `Triple.IsBaseChangeOf.flat`, `.surjective`: so is the projection `p` of a base-change square
  (`Flat` and `Surjective` are stable under base change);
* `Triple.IsBaseChangeOf.isPullback_pullbackStageHom`: the stages of `S.pullback p` are the base
  changes `(X_i)_{L,σ} = X_i ×_{Spec k} Spec L`; the stage squares of the pullback
  (`isPullback_pullbackStageHom`, for flat `p`) pasted vertically on the base-change square;
* `Triple.IsBaseChangeOf.isSmooth_pullback`: the centers `(Z_i)_{L,σ}` are smooth over `L`; the
  closed-subscheme square `AlgebraicGeometry.isPullback_subschemeι_comap` pasted on the stage square
exhibits
  `V((Z_i)_{L,σ}) → Spec L` as the base change of `V(Z_i) → Spec k`, and smoothness is stable
  under base change;
* `Triple.IsBaseChangeOf.noEmptyCenters_pullback`: no center becomes empty; the stage lifts of the
  surjective flat `p` are surjective (`surjective_pullbackStageHom`) and the inverse image of a
  proper ideal sheaf along a surjective morphism is proper (`support_comap`).

The order along the centers and the simple normal crossings under a field extension, and the
construction `Triple.baseChange`, are in `Hironaka/Scheme/BlowUpSequence/BaseChangeOrder.lean`,
`BaseChangeParameters.lean` and `BaseChangeTriple.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits Scheme.BlowUpSequence

namespace Hironaka

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-- `Spec σ` is flat and surjective for a field extension `σ : k → L` (Kollár's
`Spec L → Spec K`, "possibly not of finite type", [Kol07, 34.2]): `σ` is faithfully flat, `L`
being a nonzero free `k`-module. -/
theorem _root_.AlgebraicGeometry.flat_and_surjective_specMap (σ : k →+* L) :
    Flat (Spec.map (CommRingCat.ofHom σ)) ∧ Surjective (Spec.map (CommRingCat.ofHom σ)) := by
  rw [flat_and_surjective_SpecMap_iff, CommRingCat.hom_ofHom]
  let _ := σ.toAlgebra
  change Module.FaithfullyFlat k L
  infer_instance

end Hironaka

namespace AlgebraicGeometry.Triple.IsBaseChangeOf

open Hironaka

variable {k : Type u} [Field k] {L : Type u} [Field L]

open Scheme AlgebraicGeometry

variable {T : Triple k} {T' : Triple L} {σ : k →+* L} {p : T'.X.left ⟶ T.X.left}

/-- The projection `p : X_{L,σ} → X` of a base-change square is flat, being the base change of the
flat `Spec σ`. -/
theorem flat (hp : T'.IsBaseChangeOf T σ p) : Flat p :=
  property_of_isPullback @Flat hp.1 (flat_and_surjective_specMap σ).1

/-- The projection of a base-change square is surjective, being the base change of the surjective
`Spec σ`. -/
theorem surjective (hp : T'.IsBaseChangeOf T σ p) : Function.Surjective p :=
  haveI : Surjective p :=
    property_of_isPullback @Surjective hp.1 (flat_and_surjective_specMap σ).2
  p.surjective

/-- The stages of the pulled-back sequence are the base changes `(X_i)_{L,σ}` of the stages
[Kol07, 34.2]: the stage square of the pullback (for flat `p`) pasted on the base-change
square. -/
theorem isPullback_pullbackStageHom (hp : T'.IsBaseChangeOf T σ p) (S : BlowUpSequence T.X.left)
    (i : Fin (S.length + 1)) :
    IsPullback (S.pullbackStageHom p i)
      ((S.pullback p).stageMap (S.pullbackStageIdx p i) ≫ (T'.X.left ↘ Spec (.of L)))
      (S.stageMap i ≫ (T.X.left ↘ Spec (.of k))) (Spec.map (CommRingCat.ofHom σ)) :=
  haveI := hp.flat
  (AlgebraicGeometry.isPullback_pullbackStageHom S p i).paste_vert hp.1

/-- The base change of a smooth blow-up sequence is smooth over `L` (the centers `(Z_i)_{L,σ}` of
[Kol07, 34.2]): `V((Z_i)_{L,σ}) → Spec L` is the base change of `V(Z_i) → Spec k` along `Spec σ`
(the closed-subscheme square pasted on the stage square), and smoothness is stable under base
change. -/
theorem isSmooth_pullback (hp : T'.IsBaseChangeOf T σ p) {S : BlowUpSequence T.X.left}
    (hS : S.IsSmooth (T.X.left ↘ Spec (.of k))) : (S.pullback p).IsSmooth
      (T'.X.left ↘ Spec (.of L)) := by
  rintro ⟨j, hj⟩
  have hj' : j < S.length := by rwa [length_pullback] at hj
  have hc : (S.pullback p).center ⟨j, hj⟩ =
      (S.center ⟨j, hj'⟩).comap (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk S p j hj'
  rw [hc]
  have hsq := hp.isPullback_pullbackStageHom S ⟨j, Nat.lt_succ_of_lt hj'⟩
  have hsub := (isPullback_subschemeι_comap (S.center ⟨j, hj'⟩)
    (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩)).flip
  have hpaste := hsub.paste_vert hsq
  have hZ : Smooth ((S.center ⟨j, hj'⟩).subschemeι ≫
      S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ (T.X.left ↘ Spec (.of k))) := hS ⟨j, hj'⟩
  exact property_of_isPullback @Smooth hpaste.flip hZ

/-- Base change along a field extension creates no empty center ([Kol07, 34.2] displays every
center, none deleted): the stage lifts of the surjective flat `p` are surjective, and the inverse
image of a proper ideal sheaf along a surjective morphism is proper. -/
theorem noEmptyCenters_pullback (hp : T'.IsBaseChangeOf T σ p) {S : BlowUpSequence T.X.left}
    (hS : S.NoEmptyCenters) : (S.pullback p).NoEmptyCenters := by
  rintro ⟨j, hj⟩ h
  have hj' : j < S.length := by rwa [length_pullback] at hj
  have hc : (S.pullback p).center ⟨j, hj⟩ =
      (S.center ⟨j, hj'⟩).comap (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk S p j hj'
  change (S.pullback p).center ⟨j, hj⟩ = ⊤ at h
  rw [hc] at h
  have := hp.flat
  have hsurj := surjective_pullbackStageHom S p hp.surjective
    ⟨j, Nat.lt_succ_of_lt hj'⟩
  apply hS ⟨j, hj'⟩
  change S.center ⟨j, hj'⟩ = ⊤
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine TopologicalSpace.Closeds.ext ?_
  rw [TopologicalSpace.Closeds.coe_bot, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ ((S.center ⟨j, hj'⟩).comap
      (S.pullbackStageHom p ⟨j, Nat.lt_succ_of_lt hj'⟩)).support :=
    (mem_support_comap_iff_apply _ _ y).mpr hx
  rw [h, Scheme.IdealSheafData.support_top] at hy
  exact hy

end AlgebraicGeometry.Triple.IsBaseChangeOf

namespace Hironaka

variable {k : Type u} [Field k] {L : Type u} [Field L]

end Hironaka
