/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.Snc.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.RelativeDimension
import Hironaka.Scheme.Snc.RestrictHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Going down: restriction of an order-`m` sequence to a hypersurface of maximal contact

[Kol07, 51.1] and the second half of [Kol07, Definition 78]: for a hypersurface of maximal contact
`H` every centre `Z_i` of a smooth blow-up sequence of order `m` starting with `(X, I)` lies in the
strict transform `H_i`, and therefore the restriction
`Π|_{H_r} : (H_r, I_r|_{H_r}, m) → ⋯ → (H_0, I|_H, m)` is a smooth blow-up sequence of order `≥ m`
starting with `(H, I|_H, m)`; restriction is injective. The proof of [Kol07, Corollary 85] adds
the divisor `E`.

* **Centres in `H_i`.** Definition 78 quantifies over every open `X' ⊆ X`; read on `X' = X`
  itself (the identity open immersion) it says `Z_i ⊆ H_i` for the given sequence
  (`strictTransformSeq_le_center_of_isDynamicMaximalContact`), which makes the restriction
  `S|_H`, the `pullback` along `H.subschemeι` ([Kol07, Definition 30.2]), a smooth blow-up
  sequence on `H` (`isSmooth_pullback_of_isDynamicMaximalContact`).
* **The order goes up under restriction.** Pointwise this is `ord_le_ord_comap`
  (`ord_p I ≤ ord_p (I|_S)`, the remark opening [Kol07, §9]); along a closed subset `Z` of a
  smooth variety, `ord_Z I ≥ m` means `ord_x I ≥ m` at every point of `Z`
  (`leOrdAlong_iff_forall_mem`), and the points of `g⁻¹(Z)` map into `Z`, so
  `ord_{g⁻¹ Z}(g^* I) ≥ m` for every morphism `g` (`leOrdAlong_comap`).
* **Lemma 62 iterated.** Kollár's `J_i := (Π_i^H)_*^{-1}(I|_H, m)` is the marked recursion of the
  restricted sequence started at `I|_H`; by [Kol07, Lemma 62] in the form of
  `Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`
  (`markedTransform_comap_blowUpMap_of_pow_dvd`, iterated as
  `IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom`) it is the restriction of the marked
  transform `(I_i, m)` to `H_i`, and for a sequence of order `m` the marked transforms are the weak
  transforms `I_i`: `J_i = I_i|_{H_i}` (`weakTransformSeq_comap_pullbackStageHom`). When `I|_H` is
  nonzero on every component of `H` and `m ≥ 1`, no centre of the restricted sequence is a component
  of its stage (`not_component_subset_center_pullback`), so the case `Z = H` in which Kollár's
  remark after Lemma 62 says the lemma fails does not arise.
* **Going down.** `isOrderGeSeq_pullback_of_strictTransformSeq_le`: the conditions (1′)–(4′) of
  [Kol07, Definition 66] for `S|_H` with the data `(I|_H, m, E|_H)`. (2′) smooth centres: from
  `Z_i ⊆ H_i`. (3′) at stage `i` the centre `Z_i ⊆ H_i` has simple normal crossings with
  `E_i + H_i` (`hasSncWith_totalTransformSeq_append`), hence, viewed in `H_i`, with `E_i|_{H_i}`
  (`AlgebraicGeometry.hasSncWith_comap_of_isClosedImmersion`), which is `(E|_H)_i`
  (`totalTransformSeq_comap_pullback`). (4′) `ord_{Z_i}(J_i) ≥ m`: `J_i = I_i|_{H_i}` and
  `ord_{Z_i} I_i = m` goes up under restriction. The static corollary
  (`isOrderGeSeq_pullback_of_isMaximalContact`) takes `Z_i ⊆ H_i` from [Kol07, Theorem 80 (1)]
  (`IsOrderSeq.strictTransformSeq_le_center_of_le_MC`); the dynamic corollary
  (`isOrderGeSeq_pullback_of_isDynamicMaximalContact`, the sentence of Definition 78 with `E = ∅`)
  from the first item, the family `∅ + H` being simple normal crossing because `H` is a smooth
  divisor (`isSnc_append_empty_of_isSmoothDivisor`). Injectivity
  (`pullback_injective_of_isDynamicMaximalContact`, [Kol07, 51.1]) is `j_* j^* B = B`
  (`pushforward_pullback_of_strictTransformSeq_le`) for sequences with centres in the `H_i`.

Going down is the "onto" half of the correspondence of [Kol07, Corollary 85]
(`Hironaka/Resolution/Algebraic/MaximalContact/GoingUpDown.lean`); the other half, going up, is
`Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-! ### Definition 78 read on `X` itself, and the injection of 51.1 -/

section Dynamic

variable (I H : X.IdealSheafData) (m : ℕ) (S : BlowUpSequence X)

/-- [Kol07, Definition 78] on the open `X' = X`: every centre of a smooth blow-up sequence of order
`m` starting with `(X, I)` lies in the strict transform of a hypersurface of maximal contact
`H`. -/
theorem strictTransformSeq_le_center_of_isDynamicMaximalContact
    (hH : IsDynamicMaximalContact f I m H) (h : S.IsOrderSeq f I (DivisorFamily.empty X) m)
    (i : Fin S.length) : S.strictTransformSeq H i.castSucc ≤ S.center i := by
  have h' : S.IsOrderSeq (𝟙 X ≫ f) (I.comap (𝟙 X)) (DivisorFamily.empty X) m := by
    rwa [Category.id_comp, comap_id]
  have := hH X (𝟙 X) S h' i
  rwa [comap_id] at this

/-- The restriction `B|_H` ([Kol07, Definition 30.2]) of a smooth blow-up sequence of order `m` for
`(X, I)` to a hypersurface of maximal contact is a smooth blow-up sequence on `H`, the first
assertion of the second half of [Kol07, Definition 78]. -/
theorem isSmooth_pullback_of_isDynamicMaximalContact (hH : IsDynamicMaximalContact f I m H)
    (h : S.IsOrderSeq f I (DivisorFamily.empty X) m) :
    (S.pullback H.subschemeι).IsSmooth (H.subschemeι ≫ f) :=
  isSmooth_pullback_of_strictTransformSeq_le S H f
    (strictTransformSeq_le_center_of_isDynamicMaximalContact f I H m S hH h) h.1

/-- The injection of [Kol07, 51.1]: two smooth blow-up sequences of order `m` for `(X, I)` with the
same restriction to a hypersurface of maximal contact are equal, since `j_* j^* B = B` when every
centre lies in the `H_i`. -/
theorem pullback_injective_of_isDynamicMaximalContact (hH : IsDynamicMaximalContact f I m H)
    {S S' : BlowUpSequence X} (h : S.IsOrderSeq f I (DivisorFamily.empty X) m)
    (h' : S'.IsOrderSeq f I (DivisorFamily.empty X) m)
    (heq : S.pullback H.subschemeι = S'.pullback H.subschemeι) : S = S' := by
  have hZ : ∀ i : Fin S.length, S.strictTransformSeq H.subschemeι.ker i.castSucc ≤ S.center i := by
    rw [ker_subschemeι]
    exact strictTransformSeq_le_center_of_isDynamicMaximalContact f I H m S hH h
  have hZ' : ∀ i : Fin S'.length,
      S'.strictTransformSeq H.subschemeι.ker i.castSucc ≤ S'.center i := by
    rw [ker_subschemeι]
    exact strictTransformSeq_le_center_of_isDynamicMaximalContact f I H m S' hH h'
  calc S = (S.pullback H.subschemeι).pushforward H.subschemeι :=
        (pushforward_pullback_of_strictTransformSeq_le S H.subschemeι hZ).symm
    _ = (S'.pullback H.subschemeι).pushforward H.subschemeι := by rw [heq]
    _ = S' := pushforward_pullback_of_strictTransformSeq_le S' H.subschemeι hZ'

end Dynamic

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

/-! ### The order along a closed subset goes up under pull-back -/

section OrderRestrict

variable (I Z : X.IdealSheafData)

include f n

/-- The inequality `ord_p I ≤ ord_p (I|_S)` opening [Kol07, §9], along a closed subset: on a smooth
variety, `ord_Z I ≥ m` gives `ord_{g⁻¹ Z}(g^* I) ≥ m` for every `g : Y ⟶ X`, since the order along
`Z` is the order at every point of `Z`, and the order at a point goes up under pull-back
(`ord_le_ord_comap`). -/
theorem leOrdAlong_comap {Y : Scheme.{u}} (g : Y ⟶ X) {m : ℕ∞} (hm : I.LeOrdAlong Z.support m) :
    (I.comap g).LeOrdAlong (Z.comap g).support m := by
  have hall := (leOrdAlong_iff_forall_mem I f n Z.support m).mp hm
  intro η hη
  have hη' : η ∈ (Z.comap g).support := hη.1
  rw [support_comap] at hη'
  exact (hall (g η) hη').trans (ord_le_ord_comap I g η)

end OrderRestrict

/-! ### Lemma 62 iterated, and the restricted sequence -/

section GoingDown

variable (I H : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ) (S : BlowUpSequence X)

include n

/-- [Kol07, Lemma 62] iterated: along a smooth blow-up sequence of order `m` for `(X, I, E)`, the
marked recursion of the restricted sequence started at `I|_H` is `I_i|_{H_i}` at every stage,
since the marked transforms of a sequence of order `m` are the weak transforms `I_i`. -/
theorem weakTransformSeq_comap_pullbackStageHom (h : S.IsOrderSeq f I E m)
    (i : Fin (S.length + 1)) :
    (S.pullback H.subschemeι).markedTransformSeq (I.comap H.subschemeι) m
        (S.pullbackStageIdx H.subschemeι i) =
      (S.weakTransformSeq I i).comap (S.pullbackStageHom H.subschemeι i) := by
  rw [← IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n h i]
  exact IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom f n H.subschemeι
    (IsOrderSeq.isOrderGeSeq f n h) i

/-- **Going down** (the second half of [Kol07, Definition 78], with the divisor `E` as in the proof
of [Kol07, Corollary 85]): for a smooth hypersurface `H` with `H + E` simple normal crossing and a
smooth blow-up sequence of order `m` for `(X, I, E)` whose centres lie in the strict transforms
`H_i`, the restriction `S|_H` is a smooth blow-up sequence of order `≥ m` starting with
`(H, I|_H, m, E|_H)`: smooth centres, simple normal crossings with `(E|_H)_i = E_i|_{H_i}`, and
`ord_{Z_i}(I_i|_{H_i}) ≥ ord_{Z_i} I_i = m`. -/
theorem isOrderGeSeq_pullback_of_strictTransformSeq_le (hH : IsSmoothDivisor H)
    (hE : (E.append H).IsSnc) (h : S.IsOrderSeq f I E m)
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq H i.castSucc ≤ S.center i) :
    (S.pullback H.subschemeι).IsOrderGeSeq (H.subschemeι ≫ f) (I.comap H.subschemeι) m
      (E.comap H.subschemeι) := by
  have hsm : S.IsSmooth f := h.1
  have hsf : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hHs : Smooth (H.subschemeι ≫ f) :=
    (AlgebraicGeometry.Scheme.smooth_iff_isRegular (H.subschemeι ≫ f)).mpr hH.1
  have hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) :=
    fun i => (h.2 i).1
  refine ⟨isSmooth_pullback_of_strictTransformSeq_le S H f hZ hsm, fun i' => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i : Fin S.length, i' = S.pullbackCenterIdx H.subschemeι i :=
    ⟨Fin.cast (length_pullback S H.subschemeι) i', Fin.ext rfl⟩
  have hstage : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap (n := n) hsm i.castSucc
  have hstage' : Smooth (S.stageMap i.castSucc ≫ f) := SmoothOfRelativeDimension.smooth n _
  have hreg : ∀ x, IsRegularLocalRing ((S.stage i.castSucc).presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk (S.stageMap i.castSucc ≫ f) x
  have hci := isClosedImmersion_pullbackStageHom S H.subschemeι i.castSucc
  have hker : (S.pullbackStageHom H.subschemeι i.castSucc).ker =
      S.strictTransformSeq H i.castSucc := by
    rw [ker_pullbackStageHom, ker_subschemeι]
  have hle : (S.pullbackStageHom H.subschemeι i.castSucc).ker ≤ S.center i := by
    rw [hker]; exact hZ i
  refine ⟨?_, ?_⟩
  · rw [center_pullback]
    change ((S.pullback H.subschemeι).totalTransformSeq (E.comap H.subschemeι)
        (S.pullbackStageIdx H.subschemeι i.castSucc)).HasSncWith
      ((S.center i).comap (S.pullbackStageHom H.subschemeι i.castSucc))
    rw [← totalTransformSeq_comap_pullback f S H E hsm hHs hE hsnc hZ i.castSucc]
    have hZsnc := hasSncWith_totalTransformSeq_append f S H E hsm hE hsnc hZ i
    rw [← hker] at hZsnc
    exact hasSncWith_comap_of_isClosedImmersion _ hreg hZsnc hle
  · rw [center_pullback]
    change ((S.pullback H.subschemeι).markedTransformSeq (I.comap H.subschemeι) m
        (S.pullbackStageIdx H.subschemeι i.castSucc)).LeOrdAlong
      ((S.center i).comap (S.pullbackStageHom H.subschemeι i.castSucc)).support (m : ℕ∞)
    rw [weakTransformSeq_comap_pullbackStageHom f n I H E m S h i.castSucc]
    exact leOrdAlong_comap (S.stageMap i.castSucc ≫ f) n _ _ _
      fun η hη => ((h.2 i).2 η hη).ge

/-- Going down in the static form: for a smooth hypersurface `H` with `𝒪_X(−H) ⊆ MC(I)`, `m ≥ 1`,
and `H + E` simple normal crossing, the centres lie in the `H_i` by [Kol07, Theorem 80 (1)]
(`IsOrderSeq.strictTransformSeq_le_center_of_le_MC`) and
`isOrderGeSeq_pullback_of_strictTransformSeq_le` applies. -/
theorem isOrderGeSeq_pullback_of_isMaximalContact (hm : 1 ≤ m) (hH : IsSmoothDivisor H)
    (hE : (E.append H).IsSnc) (hMC : IsMaximalContact f I m H) (h : S.IsOrderSeq f I E m) :
    (S.pullback H.subschemeι).IsOrderGeSeq (H.subschemeι ≫ f) (I.comap H.subschemeι) m
      (E.comap H.subschemeι) :=
  isOrderGeSeq_pullback_of_strictTransformSeq_le f n I H E m S hH hE h
    fun i => IsOrderSeq.strictTransformSeq_le_center_of_le_MC f n hm h hH hMC i

/-- The second half of [Kol07, Definition 78] as printed: going down in the dynamic form with the
empty divisor family; the family `∅ + H` is simple normal crossing because `H` is a smooth
divisor. -/
theorem isOrderGeSeq_pullback_of_isDynamicMaximalContact (hH : IsSmoothDivisor H)
    (hdyn : IsDynamicMaximalContact f I m H) (h : S.IsOrderSeq f I (DivisorFamily.empty X) m) :
    (S.pullback H.subschemeι).IsOrderGeSeq (H.subschemeι ≫ f) (I.comap H.subschemeι) m
      (DivisorFamily.empty H.subscheme) := by
  have hsf : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hE : ((DivisorFamily.empty X).append H).IsSnc :=
    isSnc_append_empty_of_isSmoothDivisor (fun x => isRegularLocalRing_stalk f x) hH
  have := isOrderGeSeq_pullback_of_strictTransformSeq_le f n I H (DivisorFamily.empty X) m S hH hE
    h (strictTransformSeq_le_center_of_isDynamicMaximalContact f I H m S hdyn h)
  rwa [empty_comap] at this

/-- The case `Z = H` of Kollár's remark after [Kol07, Lemma 62] does not arise: when `I|_H` is
nonzero on every irreducible component of `H` and `m ≥ 1`, no centre of the restricted sequence
contains an irreducible component of its stage (`IsOrderGeSeq.not_component_subset_center` on the
restricted sequence). -/
theorem not_component_subset_center_pullback (hH : IsSmoothDivisor H) (hE : (E.append H).IsSnc)
    (h : S.IsOrderSeq f I E m)
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq H i.castSucc ≤ S.center i)
    (hI : IsNonzeroEverywhere (I.comap H.subschemeι)) (hm : 1 ≤ m)
    (i : Fin (S.pullback H.subschemeι).length)
    (W : Set ((S.pullback H.subschemeι).stage i.castSucc))
    (hW : W ∈ irreducibleComponents ((S.pullback H.subschemeι).stage i.castSucc)) :
    ¬ W ⊆ (((S.pullback H.subschemeι).center i).support :
      Set ((S.pullback H.subschemeι).stage i.castSucc)) := by
  have : SmoothOfRelativeDimension (n - 1) (H.subschemeι ≫ f) :=
    smoothOfRelativeDimension_of_isSmoothDivisor f n H hH
  exact IsOrderGeSeq.not_component_subset_center (H.subschemeι ≫ f) (n - 1)
    (isOrderGeSeq_pullback_of_strictTransformSeq_le f n I H E m S hH hE h hZ) hI hm i W hW

end GoingDown

end Hironaka.Sequence
