/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Collapse
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Sequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The disjoined triple `(X', π^* I, E^0 + E^1 + ⋯ + E^{k-1})`

After the `k − 1` disjoining steps "we get rid of all pairwise intersections as well"
[Kol07, 72]: the end result is `π : X' → X` with `E^0 := π^{-1}_*(E_1 + ⋯ + E_k)` a smooth
divisor, and with `E^1, …, E^{k-1}` the birational transforms of the exceptional divisors
`F^1, …, F^{k-1}`, the triple `(X', π^* I, ∑_{i=0}^{k-1} E^i)` satisfies the assumptions of
Theorem 68. The assumptions are those of a triple
[Kol07, Notation 64]: `X'` is smooth and equidimensional over `k` (along the sequence), `π^* I` is
nonzero on every component (the stalk maps of a smooth blow-up of a smooth scheme are injective:
over the center by the chart description of the blow-up, off it because the blow-up is a local
isomorphism), and the ordered family `E^0 < E^1 < ⋯ < E^{k-1}`, the total transform with the
birational transforms of the original components collapsed into `E^0`, is snc because those
transforms are pairwise disjoint (`meetLocus_strictTransformSeq_disjoinSeq`) and collapsing
pairwise disjoint components of an snc family gives an snc family (`isSnc_collapse`); `E^0` is
then a smooth divisor.

* `isNonzeroEverywhere_comap_blowUpπ`, `isNonzeroEverywhere_comap_composite_of_isSmooth`: the
  transport of "nonzero on every component" along smooth blow-ups (which are not flat, so
  `isNonzeroEverywhere_comap_of_flat` does not apply).
* `disjoinedFamily_component_bot`, `disjoinedFamily_component_coe`, `card_disjoinedFamily`: the
  shape of Kollár's family.
* `disjoinedFamily_isSnc`, `isSmoothDivisor_disjoinedFamily_bot`,
  `smoothOfRelativeDimension_composite_disjoinSeq`,
  `isNonzeroEverywhere_comap_composite_disjoinSeq`: the assumptions of Theorem 68.
* `Hironaka.disjoinedTriple`: the disjoined triple, the input of the marked order
  reduction functor in the construction of the principalization functor
  (`Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization.lean`).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal
  Scheme.IdealSheafData Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Nonzero

/-- The inverse image of an ideal sheaf nonzero on every component under a smooth blow-up of a
smooth scheme is nonzero on every component (the condition on the ideal of a triple in
[Kol07, Notation 64]): the stalk maps of the blow-up are injective (over the center by the chart
description of the blow-up, an isomorphism off it). -/
theorem isNonzeroEverywhere_comap_blowUpπ (f : X ⟶ Spec (.of k)) [Smooth f] (Z : X.IdealSheafData)
    [Smooth (Z.subschemeι ≫ f)] {I : X.IdealSheafData} (hI : IsNonzeroEverywhere I) :
    IsNonzeroEverywhere (I.comap Z.blowUpπ) := by
  intro x'
  have hinj : Function.Injective (Z.blowUpπ.stalkMap x') := by
    by_cases hx : Z.blowUpπ x' ∈ Z.support
    · exact injective_stalkMap_blowUpπ_of_mem f Z x' hx
    · have hx' : x' ∉ (Z.comap Z.blowUpπ).support := by
        rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage]
        exact hx
      have := isIso_stalkMap_π_of_notMem_support Z hx'
      exact (ConcreteCategory.bijective_of_isIso _).1
  change (I.comap Z.blowUpπ).stalkIdeal x' ≠ ⊥
  rw [stalkIdeal_comap]
  exact (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr (hI _)

/-- Along a smooth blow-up sequence of a smooth scheme, the inverse image of an ideal sheaf nonzero
on every component is nonzero on every component [Kol07, 72 and Notation 64]. -/
theorem isNonzeroEverywhere_comap_composite_of_isSmooth [PerfectField k] :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (S : BlowUpSequence X) (_ : S.IsSmooth f)
    {I : X.IdealSheafData} (_ : IsNonzeroEverywhere I), IsNonzeroEverywhere (I.comap S.composite)
  | X, _, _, nil _, _, I, hI => by
    change IsNonzeroEverywhere (I.comap (𝟙 X))
    rwa [comap_id]
  | X, f, _, cons _ D rest, hS, I, hI => by
    rw [isSmooth_cons_iff] at hS
    obtain ⟨hD, hrest⟩ := hS
    have : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
    change IsNonzeroEverywhere (I.comap (rest.composite ≫ D.blowUpπ))
    rw [comap_comp]
    exact isNonzeroEverywhere_comap_composite_of_isSmooth (D.blowUpπ ≫ f) rest hrest
      (isNonzeroEverywhere_comap_blowUpπ f D hI)

end Nonzero

section Family

variable (E : DivisorFamily X)

/-- `E^0 = π^{-1}_*(E_1 + ⋯ + E_k)` [Kol07, 72], the divisor of the final birational transforms of
the components. -/
theorem disjoinedFamily_component_bot :
    (collapsedFamily (disjoinSeq E) E).component (⊥ : WithBot _) =
      ∏ a, (disjoinSeq E).strictTransformSeq (E.component a) (Fin.last _) := by
  classical
  unfold collapsedFamily
  rw [collapse_component_bot]
  refine (Finset.prod_equiv
    (Equiv.ofInjective _ (originalIdx_injective (disjoinSeq E) E (Fin.last _)) :
      E.ι ≃ {a : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι //
        a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _))})
    (fun i => ?_) fun a _ => ?_).symm
  · simp only [Finset.mem_univ]
  · exact (component_originalIdx (disjoinSeq E) E (Fin.last _) a).symm

/-- "Let `E^1, …, E^{k-1}` denote the birational transforms of `F^1, …, F^{k-1}`" [Kol07, 72]: the
other components of the disjoined family are the remaining components of the total transform, in
its order. -/
theorem disjoinedFamily_component_coe
    (a : {a : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι //
      ¬ a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _))}) :
    (collapsedFamily (disjoinSeq E) E).component (a : WithBot _) =
      ((disjoinSeq E).totalTransformSeq E (Fin.last _)).component a.1 := rfl

/-- The index set of the total transform at stage `i` has `i` more members than `E`. -/
theorem card_ι_totalTransformSeq : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X)
    (i : Fin (S.length + 1)), Fintype.card (S.totalTransformSeq E i).ι = Fintype.card E.ι + i.val
  | _, nil _, E, i => by
    change Fintype.card E.ι = Fintype.card E.ι + i.val
    rw [Fin.val_eq_zero i, add_zero]
  | _, cons _ _ _, E, ⟨0, _⟩ => (add_zero _).symm
  | _, cons _ D rest, E, ⟨j + 1, h⟩ => by
    rw [totalTransformSeq_cons_succ, card_ι_totalTransformSeq rest (E.totalTransform D)]
    change Fintype.card (E.ι ⊕ₗ PUnit.{u + 1}) + j = _
    rw [Fintype.card_congr (toLex : E.ι ⊕ PUnit.{u + 1} ≃ E.ι ⊕ₗ PUnit.{u + 1}).symm,
      Fintype.card_sum, Fintype.card_punit, Fin.val_mk]
    omega

/-- The disjoined family has `E^0` and one `E^j` per step [Kol07, 72]. -/
theorem card_disjoinedFamily :
    Fintype.card (collapsedFamily (disjoinSeq E) E).ι = (disjoinSeq E).length + 1 := by
  classical
  change Fintype.card (WithBot {a : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι //
    ¬ a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _))}) = _
  have h1 : Fintype.card (WithBot {a : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι //
      ¬ a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _))}) =
      Fintype.card (Option {a : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι //
      ¬ a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _))}) :=
    Fintype.card_congr (Equiv.refl _)
  have h2 : Fintype.card {a : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι //
      a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _))} = Fintype.card E.ι :=
    (Fintype.card_congr (Equiv.refl _)).trans
      (Set.card_range_of_injective (originalIdx_injective (disjoinSeq E) E (Fin.last _)))
  rw [h1, Fintype.card_option, Fintype.card_subtype_compl, h2, card_ι_totalTransformSeq,
    Fin.val_last, Nat.add_sub_cancel_left]

end Family

section Assumptions

variable [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X) (hE : E.IsSnc)
include f hE

/-- `∑_{i=0}^{k-1} E^i` is a simple normal crossing divisor with the ordered index set
`E^0 < ⋯ < E^{k-1}` [Kol07, 72 and Notation 64]. -/
theorem disjoinedFamily_isSnc : (collapsedFamily (disjoinSeq E) E).IsSnc := by
  have hsm : Smooth ((disjoinSeq E).composite ≫ f) :=
    IsSmooth.smooth_stageMap' (disjoinSeq_isSmooth f E hE) (Fin.last _)
  refine isSnc_collapse ((disjoinSeq E).composite ≫ f)
    (isSnc_totalTransformSeq_disjoinSeq f E hE (Fin.last _)) ?_
  rintro x a b ⟨i, rfl⟩ ⟨j, rfl⟩ hxi hxj
  rw [component_originalIdx] at hxi hxj
  by_contra hne
  have hij : i ≠ j := fun h => hne (h ▸ rfl)
  have hx : x ∈ meetLocus
      (fun a => (disjoinSeq E).strictTransformSeq (E.component a) (Fin.last _)) 2 :=
    (mem_meetLocus_iff _ _ _).mpr ⟨{i, j}, Finset.card_pair hij, by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hxi
      · rw [Finset.mem_singleton.mp hl]
        exact hxj⟩
  rw [meetLocus_strictTransformSeq_disjoinSeq f E hE] at hx
  exact False.elim hx

/-- "`E^0 := π^{-1}_*(E_1 + ⋯ + E_k)` is a smooth divisor" [Kol07, 72]. -/
theorem isSmoothDivisor_disjoinedFamily_bot :
    IsSmoothDivisor
      ((collapsedFamily (disjoinSeq E) E).component (⊥ : WithBot _)) := by
  have hsm : Smooth ((disjoinSeq E).composite ≫ f) :=
    IsSmooth.smooth_stageMap' (disjoinSeq_isSmooth f E hE) (Fin.last _)
  have hsnc := disjoinedFamily_isSnc f E hE
  exact isSmoothDivisor_of_snc_data (collapsedFamily (disjoinSeq E) E).component hsnc.1
    (fun x => hsnc.2 x)
    (fun x => isRegularLocalRing_stalk ((disjoinSeq E).composite ≫ f) x) _

/-- `π^* I` is nonzero on every component of `X'` [Kol07, 72 and Notation 64]. -/
theorem isNonzeroEverywhere_comap_composite_disjoinSeq {I : X.IdealSheafData}
    (hI : IsNonzeroEverywhere I) : IsNonzeroEverywhere (I.comap (disjoinSeq E).composite) :=
  isNonzeroEverywhere_comap_composite_of_isSmooth f _ (disjoinSeq_isSmooth f E hE) hI

end Assumptions

/-- `X'` is smooth and equidimensional over `k` [Kol07, 72 and Notation 64]. -/
theorem smoothOfRelativeDimension_composite_disjoinSeq [PerfectField k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : DivisorFamily X) (hE : E.IsSnc) :
    SmoothOfRelativeDimension n ((disjoinSeq E).composite ≫ f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact IsSmooth.smoothOfRelativeDimension_stageMap (disjoinSeq_isSmooth f E hE) (Fin.last _)

end Hironaka.Sequence

/-! ### The disjoined triple -/

namespace Hironaka

open Hironaka.Sequence AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- **The disjoined triple** `(X', π^* I, ∑_{i=0}^{k-1} E^i)` of [Kol07, 72], with `π : X' → X`
the disjoining sequence of `T.E`, `π^* I` its inverse image ideal sheaf and the ordered family
`E^0 < E^1 < ⋯ < E^{k-1}` of `collapsedFamily`; it "satisfies the assumptions of (68)". -/
noncomputable def disjoinedTriple (T : Triple k) : Triple k where
  X := .ofHom ((disjoinSeq T.E).composite ≫ (T.X.left ↘ Spec (.of k)))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have : IsProper (disjoinSeq T.E).composite := isProper_stageMap (disjoinSeq T.E) (Fin.last _)
      exact inferInstanceAs (FiniteType ((disjoinSeq T.E).composite ≫ (T.X.left ↘ Spec (.of k)))))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have : IsProper (disjoinSeq T.E).composite := isProper_stageMap (disjoinSeq T.E) (Fin.last _)
      exact inferInstanceAs (IsSeparated ((disjoinSeq T.E).composite ≫ (T.X.left ↘ Spec (.of k)))))
  smoothOfRelativeDimension := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact ⟨n, IsSmooth.smoothOfRelativeDimension_stageMap (n := n)
      (disjoinSeq_isSmooth (T.X.left ↘ Spec (.of k)) T.E T.isSnc) (Fin.last _)⟩
  I := T.I.comap (disjoinSeq T.E).composite
  isNonzeroEverywhere :=
    isNonzeroEverywhere_comap_composite_disjoinSeq (T.X.left ↘ Spec (.of k)) T.E T.isSnc
      T.isNonzeroEverywhere
  E := collapsedFamily (disjoinSeq T.E) T.E
  isSnc := disjoinedFamily_isSnc (T.X.left ↘ Spec (.of k)) T.E T.isSnc

end Hironaka
