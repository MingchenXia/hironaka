/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.Functor
import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Functoriality for smooth morphisms: blow-up sequence functors and pullback

A blow-up sequence functor `B` commutes with a smooth morphism `h : Y → X` when
`B(Y, h^* I, h^{-1}(E)) = h^* B(X, I, E)`, and it commutes with smooth morphisms when it commutes
with every smooth surjection and, for every smooth `h`, `B(Y, h^* I, h^{-1}(E))` is the pull-back
`h^* B(X, I, E)` with its empty blow-ups deleted [Kol07, 34.1]. The predicates are
`AlgebraicGeometry.Triple.IsPullbackOf T' T h` (the triple `T'` carries the pullback data of `T`
along `h`) and, on the functors of `Hironaka/Scheme/BlowUpSequence/Functor.lean`, `CommutesWith`,
`CommutesWithSmoothSurjections`, `CommutesWithSmooth`
(`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`). This module proves the basic facts
about them.

* **Pullback data** (`isPullbackOf_pullback`, `IsPullbackOf.comp`): the pullback of a triple
  (`Hironaka/Scheme/BlowUpSequence/Pullback.lean`) carries the pullback data by construction (its
  ambient scheme is `Y`, its ideal and family the inverse images, `h` over `Spec k` by hypothesis),
  and pullback data compose along `f ≫ g` because `comap` does (`comap_comp`;
  `DivisorFamily.comap_comp` componentwise).
* **Commuting with the identity and with composites** (`commutesWith_id`, `commutesWith_comp`):
  the functoriality of the pull-back `h^*` of [Kol07, 30.1] (`pullback_id`, `pullback_comp`).
* **The two bullets** (`eraseEmpty_pullback_of_surjective`, `commutesWithSmooth_iff`): along a
  smooth surjection the pulled-back value has no empty blow-ups (its centers are the inverse
  images of the nonempty centers under the stage lifts, which are surjective by base change, and
  the inverse image of a nonempty closed subscheme under a surjection is nonempty), so the second
  bullet of [Kol07, 34.1] implies the first.
* **Locality** (`eq_of_pullback_of_covers`, `eq_of_pullback_openCover`,
  `commutesWith_of_openCover`, `commutesWith_of_surjective_comp`): two blow-up sequences agreeing
  after pullback to every member of a covering family of open immersions are equal, by induction
  on the sequence: the first centers agree because ideal sheaves are determined by their stalks
  (`ext_stalkIdeal`) and an open immersion is an isomorphism on stalks; the tails are pulled back
  along the lifted family `blowUpMap (g i) D`, again open immersions covering the blow-up
  (`isPullback_blowUpMap`, `range_fst_of_isPullback`). The nonempty index type is needed: on the
  empty scheme, sequences of every length have the same vacuous pullbacks along an empty cover.
  The surjective form is `pullback_injective_of_surjective` with `pullback_comp`. This is Kollár's
  remark that the functoriality isomorphism is unique when it exists, so that its existence is a
  local question [Kol07, 34].
* **The order predicates along pullback data** (`IsPullbackOf.isOrderSeq_pullback` and the three
  related lemmas): the transport of the order conditions along a pullback in the form needed when
  one holds the pulled-back triple: the equidimensionality of `T'` (`T'.smoothOfRelativeDimension`,
  transported along `h ≫ f = f'`) replaces the relative dimension of `h`, through the `_of_equidim`
  forms in `PullbackInduced.lean`, `PullbackSnc.lean` and `PullbackEraseEmpty.lean`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry.Scheme

namespace DivisorFamily

variable {X Y Z : Scheme.{u}}

/-- Pulling a divisor family back along a composite is pulling back in two steps. -/
theorem comap_comp (E : DivisorFamily X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    E.comap (f ≫ g) = (E.comap g).comap f := by
  obtain ⟨ι, c⟩ := E
  change DivisorFamily.mk ι (fun i => (c i).comap (f ≫ g)) =
    DivisorFamily.mk ι (fun i => ((c i).comap g).comap f)
  simp only [Scheme.IdealSheafData.comap_comp]

/-- Pulling back an `append` is the `append` of the pullbacks. -/
theorem comap_append (E : DivisorFamily X) (J : X.IdealSheafData) (h : Y ⟶ X) :
    (E.append J).comap h = (E.comap h).append (J.comap h) := by
  change DivisorFamily.mk (E.ι ⊕ₗ PUnit.{u + 1})
      (fun i => (Sum.elim E.component (fun _ => J) (ofLex i)).comap h) =
    DivisorFamily.mk (E.ι ⊕ₗ PUnit.{u + 1})
      (fun i => Sum.elim (fun a => (E.component a).comap h) (fun _ => J.comap h) (ofLex i))
  congr 1
  funext i
  rcases i with a | u <;> rfl

end DivisorFamily

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The inverse image of an ideal sheaf under a surjection is the unit ideal only if the ideal
sheaf is: supports pull back to preimages (Mathlib's `support_comap`). -/
theorem eq_top_of_comap_eq_top_of_surjective (I : X.IdealSheafData) (f : Y ⟶ X)
    (hs : Function.Surjective f) (h : I.comap f = ⊤) : I = ⊤ := by
  rw [← support_eq_bot_iff] at h ⊢
  rw [support_comap] at h
  refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => (Set.notMem_empty x hx).elim⟩
  obtain ⟨y, rfl⟩ := hs x
  have hy : y ∈ I.support.preimage f.continuous := hx
  rw [h] at hy
  exact (Set.notMem_empty y hy).elim

/-- Ideal sheaves agreeing on a covering family of open immersions agree: by stalks
(`ext_stalkIdeal`), an open immersion being an isomorphism on stalks. -/
theorem eq_of_comap_eq_of_covers {σ : Type u} {W : σ → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x, ∃ i w, g i w = x) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (g i) = J.comap (g i)) : I = J := by
  refine ext_stalkIdeal fun x => ?_
  obtain ⟨i, w, rfl⟩ := hcov x
  have h1 := congrArg (fun K : (W i).IdealSheafData => K.stalkIdeal w) (h i)
  simp only [stalkIdeal_comap] at h1
  have hb : Function.Bijective ((g i).stalkMap w).hom :=
    (asIso ((g i).stalkMap w)).commRingCatIsoToRingEquiv.bijective
  rw [← Ideal.comap_map_of_bijective _ hb (I := I.stalkIdeal (g i w)), h1,
    Ideal.comap_map_of_bijective _ hb]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {Y : Scheme.{u}}

/-- Two blow-up sequences on `Y` agreeing after pullback to every member of a nonempty covering
family of open immersions are equal ([Kol07, 34]: the existence of the functoriality isomorphism
is a local question), by induction on the sequence: `eq_of_comap_eq_of_covers` for the first
centers and the lifted family `blowUpMap (g i) D` (open immersions covering the blow-up) for the
tails. -/
theorem eq_of_pullback_of_covers {σ : Type u} [Nonempty σ] (S : BlowUpSequence Y) :
    ∀ (S' : BlowUpSequence Y) {W : σ → Scheme.{u}} (g : ∀ i, W i ⟶ Y) [∀ i, IsOpenImmersion (g i)],
      (∀ y, ∃ i w, g i w = y) → (∀ i, S.pullback (g i) = S'.pullback (g i)) → S = S' := by
  induction S with
  | nil Y =>
    intro S' W g _ hcov h
    obtain ⟨i⟩ := ‹Nonempty σ›
    cases S' with
    | nil => rfl
    | cons Y D r =>
      have := congrArg BlowUpSequence.length (h i)
      rw [length_pullback, length_pullback] at this
      exact absurd this (Nat.succ_ne_zero _).symm
  | cons Y D r ih =>
    intro S' W g _ hcov h
    obtain ⟨i₀⟩ := ‹Nonempty σ›
    cases S' with
    | nil =>
      have := congrArg BlowUpSequence.length (h i₀)
      rw [length_pullback, length_pullback] at this
      exact absurd this (Nat.succ_ne_zero _)
    | cons Y D' r' =>
      have hD : D = D' :=
        Scheme.IdealSheafData.eq_of_comap_eq_of_covers g hcov fun i => (cons_inj (h i)).1
      subst hD
      have hr : ∀ i, r.pullback (Scheme.Hom.blowUpMap (g i) D) = r'.pullback (Scheme.Hom.blowUpMap
          (g i) D) := by
        intro i
        obtain ⟨e, he⟩ := cons_inj (h i)
        exact he
      have hcov' : ∀ z, ∃ i w, Scheme.Hom.blowUpMap (g i) D w = z := by
        intro z
        obtain ⟨i, y, hy⟩ := hcov (D.blowUpπ z)
        have hrange := range_fst_of_isPullback
          (isPullback_blowUpMap (g i) D)
        have hz : z ∈ Set.range (Scheme.Hom.blowUpMap (g i) D) := by
          rw [hrange]
          exact ⟨y, hy⟩
        obtain ⟨w, hw⟩ := hz
        exact ⟨i, w, hw⟩
      exact congrArg (cons Y D) (ih r' (fun i => Scheme.Hom.blowUpMap (g i) D) hcov' hr)

/-- Two blow-up sequences on `Y` agreeing after pullback to every member of a nonempty open cover
of `Y` are equal [Kol07, 34]. -/
theorem eq_of_pullback_openCover {S S' : BlowUpSequence Y} (𝒰 : Scheme.OpenCover.{u} Y)
    [Nonempty 𝒰.I₀] (h : ∀ i, S.pullback (𝒰.f i) = S'.pullback (𝒰.f i)) : S = S' :=
  eq_of_pullback_of_covers S S' 𝒰.f (fun y => 𝒰.exists_eq y) h

end AlgebraicGeometry

namespace Hironaka

variable {k : Type u} [Field k]

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

open Scheme

/-- The pullback of a triple along a smooth morphism carries the pullback data
`(Y, h^* I, h^{-1}(E))` of [Kol07, 34.1]. -/
theorem isPullbackOf_pullback [PerfectField k] (T : Triple k) {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k))) (h : Y ⟶ T.X.left)
    [h.IsOver (Spec (.of k))] [Smooth h] : (Triple.pullback T hY h).IsPullbackOf T h :=
  ⟨HomIsOver.comp_over (f := h) (S := Spec (.of k)), rfl, rfl⟩

/-- Pullback data compose along a composite of morphisms [Kol07, 30.1]. -/
theorem IsPullbackOf.comp {T T' T'' : Triple k} {g : T'.X.left ⟶ T.X.left}
    {f : T''.X.left ⟶ T'.X.left}
    (hg : T'.IsPullbackOf T g) (hf : T''.IsPullbackOf T' f) : T''.IsPullbackOf T (f ≫ g) :=
  ⟨by rw [Category.assoc, hg.1, hf.1], by rw [hf.2.1, hg.2.1, Scheme.IdealSheafData.comap_comp],
    by rw [hf.2.2, hg.2.2, DivisorFamily.comap_comp]⟩

/-- The pullback of a smooth blow-up sequence of order `m` for `T` along a smooth `h` is one for a
triple `T'` carrying the pullback data of `T` along `h`. -/
theorem IsPullbackOf.isOrderSeq_pullback [CharZero k] {T T' : Triple k} {h : T'.X.left ⟶ T.X.left}
    [Smooth h] (hp : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left} {m : ℕ}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) :
    (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m := by
  obtain ⟨hf, hI, hE⟩ := hp
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  have : SmoothOfRelativeDimension n' (h ≫ (T.X.left ↘ Spec (.of k))) := by rw [hf]; exact hn'
  rw [hI, hE, ← hf]
  exact IsOrderSeq.pullback_of_equidim (T.X.left ↘ Spec (.of k)) n h n' hS

/-- The pullback of a smooth blow-up sequence of order `m` along a smooth `h`, with its empty
blow-ups deleted as in the second bullet of [Kol07, 34.1], is one for the pullback data. -/
theorem IsPullbackOf.isOrderSeq_eraseEmpty_pullback [CharZero k] {T T' : Triple k}
    {h : T'.X.left ⟶ T.X.left} [Smooth h] (hp : T'.IsPullbackOf T h)
    {S : BlowUpSequence T.X.left} {m : ℕ}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) :
    (S.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m := by
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  exact IsOrderSeq.eraseEmpty (T'.X.left ↘ Spec (.of k)) n' (hp.isOrderSeq_pullback hS)

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

namespace MarkedTriple

open Scheme

/-- The pullback of a marked triple along a smooth morphism carries the pullback data of
[Kol07, 34.1], with the same mark. -/
theorem isPullbackOf_pullback [PerfectField k] (T : MarkedTriple k) {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k))) (h : Y ⟶ T.X.left)
    [h.IsOver (Spec (.of k))] [Smooth h] : (MarkedTriple.pullback T hY h).IsPullbackOf T h :=
  ⟨Triple.isPullbackOf_pullback T.toTriple hY h, rfl⟩

/-- Pullback data of marked triples compose along a composite of morphisms [Kol07, 30.1]. -/
theorem IsPullbackOf.comp {T T' T'' : MarkedTriple k} {g : T'.X.left ⟶ T.X.left}
    {f : T''.X.left ⟶ T'.X.left}
    (hg : T'.IsPullbackOf T g) (hf : T''.IsPullbackOf T' f) : T''.IsPullbackOf T (f ≫ g) :=
  ⟨hg.1.comp hf.1, hf.2.trans hg.2⟩

/-- The pullback of a smooth blow-up sequence of order `≥ m` for a marked triple `T` along a
smooth `h` is one for a marked triple `T'` carrying the pullback data of `T` along `h`. -/
theorem IsPullbackOf.isOrderGeSeq_pullback [CharZero k] {T T' : MarkedTriple k}
    {h : T'.X.left ⟶ T.X.left} [Smooth h] (hp : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) :
    (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E := by
  obtain ⟨⟨hf, hI, hE⟩, hm⟩ := hp
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  rw [hI, hE, hm, ← hf]
  exact IsOrderGeSeq.pullback_of_smooth (T.X.left ↘ Spec (.of k)) n h hS

/-- The pullback of a smooth blow-up sequence of order `≥ m` along a smooth `h`, with its empty
blow-ups deleted, is one for the pullback data of the marked triple. -/
theorem IsPullbackOf.isOrderGeSeq_eraseEmpty_pullback [CharZero k] {T T' : MarkedTriple k}
    {h : T'.X.left ⟶ T.X.left} [Smooth h] (hp : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) :
    (S.pullback h).eraseEmpty.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E := by
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  exact IsOrderGeSeq.eraseEmpty (T'.X.left ↘ Spec (.of k)) n' (hp.isOrderGeSeq_pullback hS)

end MarkedTriple

namespace OrderSeqAssignment

variable {m : ℕ} {Dom : Triple k → Prop}

/-- Every functor commutes with the identity [Kol07, 34.1 and 30.1]. -/
theorem commutesWith_id (B : OrderSeqAssignment k m Dom) (T : Triple k) :
    B.CommutesWith (𝟙 T.X.left) := fun _ _ => by
  simp

/-- A functor commuting with `f` and with `g` commutes with `f ≫ g` [Kol07, 34.1 and 30.1]. -/
theorem commutesWith_comp (B : OrderSeqAssignment k m Dom) {T T' T'' : Triple k}
    {g : T'.X.left ⟶ T.X.left}
    {f : T''.X.left ⟶ T'.X.left} (hT' : Dom T') (hg : B.CommutesWith g) (hf : B.CommutesWith f) :
    B.CommutesWith (f ≫ g) := fun hT hT'' => by
  rw [hf hT' hT'', hg hT hT', pullback_comp]

/-- A functor commuting with smooth surjections commutes with each smooth surjection
[Kol07, 34.1, first bullet]. -/
theorem CommutesWithSmoothSurjections.commutesWith {B : OrderSeqAssignment k m Dom}
    (hB : B.CommutesWithSmoothSurjections) {T T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) : B.CommutesWith h :=
  hB T T' h hs hp

/-- The first bullet of [Kol07, 34.1]: a functor commuting with smooth morphisms commutes with
smooth surjections. -/
theorem CommutesWithSmooth.commutesWithSmoothSurjections {B : OrderSeqAssignment k m Dom}
    (hB : B.CommutesWithSmooth) : B.CommutesWithSmoothSurjections :=
  hB.1

/-- Along a smooth surjection the pulled-back value of a functor has no empty blow-ups
[Kol07, 34.1]: its centers are the inverse images of nonempty centers under surjective stage
lifts. -/
theorem eraseEmpty_pullback_of_surjective (B : OrderSeqAssignment k m Dom) (T : Triple k)
    (hT : Dom T)
    {Y : Scheme.{u}} (h : Y ⟶ T.X.left) [Smooth h] (hs : Function.Surjective h) :
    ((B.seq T hT).pullback h).eraseEmpty = (B.seq T hT).pullback h := by
  refine (eraseEmpty_eq_self_iff _).2 fun i hi => ?_
  obtain ⟨j, hj⟩ := i
  have hj' : j < (B.seq T hT).length := by rwa [length_pullback] at hj
  have hc : ((B.seq T hT).pullback h).center ⟨j, hj⟩ =
      ((B.seq T hT).center ⟨j, hj'⟩).comap
        ((B.seq T hT).pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk (B.seq T hT) h j hj'
  change ((B.seq T hT).pullback h).center ⟨j, hj⟩ = ⊤ at hi
  rw [hc] at hi
  exact B.center_ne_top T hT ⟨j, hj'⟩
    (Scheme.IdealSheafData.eq_top_of_comap_eq_top_of_surjective _ _
      (surjective_pullbackStageHom (B.seq T hT) h hs _) hi)

/-- Commuting with smooth morphisms is equivalent to the second bullet of [Kol07, 34.1] alone:
the first bullet follows because along a smooth surjection nothing is deleted. -/
theorem commutesWithSmooth_iff (B : OrderSeqAssignment k m Dom) :
    B.CommutesWithSmooth ↔
      ∀ (T T' : Triple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOf T h →
        ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = ((B.seq T hT).pullback h).eraseEmpty := by
  refine ⟨fun hB => hB.2, fun H => ⟨?_, H⟩⟩
  intro T T' h _ hs hp hT hT'
  rw [H T T' h hp hT hT', B.eraseEmpty_pullback_of_surjective T hT h hs]

/-- The functoriality equation of [Kol07, 34.1] is local on the source: it holds for `h` if it
holds after restriction to every member of a nonempty open cover of the source (as used in the
proof of [Kol07, Theorem 36]: "(34.1) is a local property"). -/
theorem commutesWith_of_openCover (B : OrderSeqAssignment k m Dom) {T T' : Triple k}
    (h : T'.X.left ⟶ T.X.left) (𝒰 : Scheme.OpenCover.{u} T'.X.left) [Nonempty 𝒰.I₀]
    (h𝒰 : ∀ (hT : Dom T) (hT' : Dom T') i,
      (B.seq T' hT').pullback (𝒰.f i) = (B.seq T hT).pullback (𝒰.f i ≫ h)) :
    B.CommutesWith h := fun hT hT' =>
  eq_of_pullback_openCover 𝒰 fun i => by rw [h𝒰 hT hT' i, pullback_comp]

/-- Descent of the functoriality equation along a flat surjection `g`: if `B` commutes with `g`
and with `g ≫ h`, it commutes with `h` (the pullback along a flat surjection is injective on
sequences; the argument of the proofs of [Kol07, Theorem 36 and Proposition 37]). -/
theorem commutesWith_of_surjective_comp (B : OrderSeqAssignment k m Dom) {T T' T'' : Triple k}
    (h : T'.X.left ⟶ T.X.left) (g : T''.X.left ⟶ T'.X.left) [Flat g] (hs : Function.Surjective g)
    (hT'' : Dom T'')
    (hg : B.CommutesWith g) (hgh : B.CommutesWith (g ≫ h)) : B.CommutesWith h := fun hT hT' =>
  pullback_injective_of_surjective g hs (by rw [← hg hT' hT'', hgh hT hT'', pullback_comp])

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {Dom : MarkedTriple k → Prop}

/-- Every marked functor commutes with the identity [Kol07, 34.1]. -/
theorem commutesWith_id (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) :
    B.CommutesWith (𝟙 T.X.left) := fun _ _ => by
  simp

/-- A marked functor commuting with `f` and with `g` commutes with `f ≫ g` [Kol07, 34.1]. -/
theorem commutesWith_comp (B : OrderGeSeqAssignment k Dom) {T T' T'' : MarkedTriple k}
    {g : T'.X.left ⟶ T.X.left} {f : T''.X.left ⟶ T'.X.left} (hT' : Dom T') (hg : B.CommutesWith g)
    (hf : B.CommutesWith f) : B.CommutesWith (f ≫ g) := fun hT hT'' => by
  rw [hf hT' hT'', hg hT hT', pullback_comp]

/-- A marked functor commuting with smooth surjections commutes with each smooth surjection
[Kol07, 34.1, first bullet]. -/
theorem CommutesWithSmoothSurjections.commutesWith {B : OrderGeSeqAssignment k Dom}
    (hB : B.CommutesWithSmoothSurjections) {T T' : MarkedTriple k}
    (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) : B.CommutesWith h :=
  hB T T' h hs hp

/-- The first bullet of [Kol07, 34.1] for marked functors. -/
theorem CommutesWithSmooth.commutesWithSmoothSurjections {B : OrderGeSeqAssignment k Dom}
    (hB : B.CommutesWithSmooth) : B.CommutesWithSmoothSurjections :=
  hB.1

/-- Along a smooth surjection the pulled-back value of a marked functor has no empty blow-ups. -/
theorem eraseEmpty_pullback_of_surjective (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k)
    (hT : Dom T) {Y : Scheme.{u}} (h : Y ⟶ T.X.left) [Smooth h] (hs : Function.Surjective h) :
    ((B.seq T hT).pullback h).eraseEmpty = (B.seq T hT).pullback h := by
  refine (eraseEmpty_eq_self_iff _).2 fun i hi => ?_
  obtain ⟨j, hj⟩ := i
  have hj' : j < (B.seq T hT).length := by rwa [length_pullback] at hj
  have hc : ((B.seq T hT).pullback h).center ⟨j, hj⟩ =
      ((B.seq T hT).center ⟨j, hj'⟩).comap
        ((B.seq T hT).pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk (B.seq T hT) h j hj'
  change ((B.seq T hT).pullback h).center ⟨j, hj⟩ = ⊤ at hi
  rw [hc] at hi
  exact B.center_ne_top T hT ⟨j, hj'⟩
    (Scheme.IdealSheafData.eq_top_of_comap_eq_top_of_surjective _ _
      (surjective_pullbackStageHom (B.seq T hT) h hs _) hi)

/-- Commuting with smooth morphisms is equivalent to the second bullet of [Kol07, 34.1] alone, for
marked functors. -/
theorem commutesWithSmooth_iff (B : OrderGeSeqAssignment k Dom) :
    B.CommutesWithSmooth ↔
      ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOf T h →
        ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = ((B.seq T hT).pullback h).eraseEmpty := by
  refine ⟨fun hB => hB.2, fun H => ⟨?_, H⟩⟩
  intro T T' h _ hs hp hT hT'
  rw [H T T' h hp hT hT', B.eraseEmpty_pullback_of_surjective T hT h hs]

/-- The functoriality equation is local on the source, for marked functors. -/
theorem commutesWith_of_openCover (B : OrderGeSeqAssignment k Dom) {T T' : MarkedTriple k}
    (h : T'.X.left ⟶ T.X.left) (𝒰 : Scheme.OpenCover.{u} T'.X.left) [Nonempty 𝒰.I₀]
    (h𝒰 : ∀ (hT : Dom T) (hT' : Dom T') i,
      (B.seq T' hT').pullback (𝒰.f i) = (B.seq T hT).pullback (𝒰.f i ≫ h)) :
    B.CommutesWith h := fun hT hT' =>
  eq_of_pullback_openCover 𝒰 fun i => by rw [h𝒰 hT hT' i, pullback_comp]

/-- Descent of the functoriality equation along a flat surjection, for marked functors. -/
theorem commutesWith_of_surjective_comp (B : OrderGeSeqAssignment k Dom) {T T' T'' : MarkedTriple k}
    (h : T'.X.left ⟶ T.X.left) (g : T''.X.left ⟶ T'.X.left) [Flat g] (hs : Function.Surjective g)
    (hT'' : Dom T'')
    (hg : B.CommutesWith g) (hgh : B.CommutesWith (g ≫ h)) : B.CommutesWith h := fun hT hT' =>
  pullback_injective_of_surjective g hs (by rw [← hg hT' hT'', hgh hT hT'', pullback_comp])

end OrderGeSeqAssignment

end Hironaka
