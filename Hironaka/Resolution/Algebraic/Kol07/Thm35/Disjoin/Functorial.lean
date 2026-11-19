/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of the disjoining sequence

The loci `Z_t` are defined from `E` alone, so for a smooth `h : Y → X` the disjoining sequence of
`h^{-1} E` is the pull-back of the disjoining sequence of `E` [Kol07, 72]. The proof is an
induction along the steps: the center `∏_{|s| = m} ∑_{i ∈ s} G_i` commutes with inverse images
because the inverse image ideal sheaf is multiplicative and commutes with sums
(`disjoinCenter_comap`), the pull-back of a `cons` is the `cons` of the inverse image center and
the pull-back of the tail along the induced morphism of blow-ups (`pullback_cons`), and strict
transforms commute with flat base change along that morphism (`strictTransform_comap_of_flat`).
No empty blow-up has to be deleted: the identity holds on the nose for every flat `h`
(`disjoinSeq_comap_of_flat`), in particular for smooth `h` (`disjoin_functorial`, the
functoriality of [Kol07, 34.1]) and for the base-change squares of [Kol07, 34.2], which are flat;
the "up to empty blow-ups" of Kollár's parenthetical remark concerns the alternative construction
with `dim X`-fold intersections, and the form with the empty blow-ups deleted is
`disjoin_functorial_eraseEmpty`.

Kollár's first paragraph, "we should not introduce arbitrary choices in the process", is the
statement `disjoinSeq_of_equiv`: the sequence does not depend on the order of the index set.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {ι : Type*} [Fintype ι]

/-- The disjoining steps of the inverse images are the pull-back of the disjoining steps, on the
nose, for flat `h` [Kol07, 72]. -/
theorem disjoinSeqAux_comap_of_flat : ∀ (m : ℕ) {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    (G : ι → X.IdealSheafData),
    disjoinSeqAux m (fun i => (G i).comap h) = (disjoinSeqAux m G).pullback h
  | 0, _, _, h, _, _ => (pullback_nil h).symm
  | 1, _, _, h, _, _ => (pullback_nil h).symm
  | m + 2, X, Y, h, _, G => by
    rw [disjoinSeqAux_succ_succ, disjoinSeqAux_succ_succ, pullback_cons]
    have hflat : Flat (Scheme.Hom.blowUpMap h (disjoinCenter G (m + 2))) :=
      property_of_isPullback _
        (isPullback_blowUpMap h (disjoinCenter G (m + 2))) inferInstance
    have key : ∀ {Z' : Y.IdealSheafData} (_ : Z' = (disjoinCenter G (m + 2)).comap h),
        HEq (disjoinSeqAux (m + 1) fun i => ((G i).comap h).strictTransform Z')
          ((disjoinSeqAux (m + 1) fun i => (G i).strictTransform (disjoinCenter G (m + 2))).pullback
            (Scheme.Hom.blowUpMap h (disjoinCenter G (m + 2)))) := by
      intro Z' hZ
      subst hZ
      refine heq_of_eq ?_
      have hst : (fun i => ((G i).comap h).strictTransform ((disjoinCenter G (m + 2)).comap h)) =
          fun i => ((G i).strictTransform (disjoinCenter G (m + 2))).comap
            (Scheme.Hom.blowUpMap h (disjoinCenter G (m + 2))) :=
        funext fun i => strictTransform_comap_of_flat h _ _
      rw [hst]
      exact disjoinSeqAux_comap_of_flat (m + 1) (Scheme.Hom.blowUpMap h (disjoinCenter G (m + 2))) _
    exact cons_congr (disjoinCenter_comap h G (m + 2)) (key (disjoinCenter_comap h G (m + 2)))

/-- For a flat `h : Y ⟶ X` the disjoining sequence of `h^{-1} E` is the pull-back
([Kol07, 30.1]) of the disjoining sequence of `E` [Kol07, 72], with no empty blow-up to delete. -/
theorem disjoinSeq_comap_of_flat (h : Y ⟶ X) [Flat h] (E : DivisorFamily X) :
    disjoinSeq (E.comap h) = (disjoinSeq E).pullback h :=
  disjoinSeqAux_comap_of_flat (Fintype.card E.ι) h E.component

/-- The disjoining commutes with smooth morphisms [Kol07, 72 and 34.1]. -/
theorem disjoin_functorial (h : Y ⟶ X) [Smooth h] (E : DivisorFamily X) :
    disjoinSeq (E.comap h) = (disjoinSeq E).pullback h :=
  disjoinSeq_comap_of_flat h E

/-- The disjoining commutes with smooth morphisms up to the deletion of empty blow-ups, the form
of the second clause of [Kol07, 34.1]. -/
theorem disjoin_functorial_eraseEmpty (h : Y ⟶ X) [Smooth h] (E : DivisorFamily X) :
    (disjoinSeq (E.comap h)).eraseEmpty = ((disjoinSeq E).pullback h).eraseEmpty :=
  congrArg BlowUpSequence.eraseEmpty (disjoin_functorial h E)

section Reindex

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The center does not depend on the indexing of the members. -/
theorem disjoinCenter_equiv (σ : ι₁ ≃ ι₂) {G₁ : ι₁ → X.IdealSheafData} {G₂ : ι₂ → X.IdealSheafData}
    (hσ : ∀ a, G₂ (σ a) = G₁ a) (m : ℕ) : disjoinCenter G₂ m = disjoinCenter G₁ m := by
  unfold disjoinCenter
  symm
  refine Finset.prod_equiv σ.finsetCongr (fun s => ?_) fun s _ => ?_
  · simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Equiv.finsetCongr_apply,
      Finset.card_map]
  · rw [Equiv.finsetCongr_apply, ← Finset.sup_eq_iSup, ← Finset.sup_eq_iSup, Finset.sup_map]
    exact Finset.sup_congr rfl fun i _ => (hσ i).symm

/-- The disjoining steps do not depend on the indexing of the members. -/
theorem disjoinSeqAux_equiv : ∀ (m : ℕ) {X : Scheme.{u}} (σ : ι₁ ≃ ι₂) {G₁ : ι₁ → X.IdealSheafData}
    {G₂ : ι₂ → X.IdealSheafData} (_ : ∀ a, G₂ (σ a) = G₁ a),
    disjoinSeqAux m G₂ = disjoinSeqAux m G₁
  | 0, _, _, _, _, _ => rfl
  | 1, _, _, _, _, _ => rfl
  | m + 2, X, σ, G₁, G₂, hσ => by
    rw [disjoinSeqAux_succ_succ, disjoinSeqAux_succ_succ]
    have key : ∀ {Z : X.IdealSheafData} (_ : Z = disjoinCenter G₁ (m + 2)),
        HEq (disjoinSeqAux (m + 1) fun i => (G₂ i).strictTransform Z)
          (disjoinSeqAux (m + 1) fun i => (G₁ i).strictTransform (disjoinCenter G₁ (m + 2))) := by
      intro Z hZ
      subst hZ
      exact heq_of_eq (disjoinSeqAux_equiv (m + 1) σ fun a => by rw [hσ a])
    exact cons_congr (disjoinCenter_equiv σ hσ (m + 2)) (key (disjoinCenter_equiv σ hσ (m + 2)))

/-- "We should not introduce arbitrary choices in the process" [Kol07, 72]: the disjoining
sequence does not depend on the order of the index set; two families with the same components
under a bijection of indices have the same disjoining sequence. -/
theorem disjoinSeq_of_equiv {E₁ E₂ : DivisorFamily X} (σ : E₁.ι ≃ E₂.ι)
    (hσ : ∀ a, E₂.component (σ a) = E₁.component a) : disjoinSeq E₂ = disjoinSeq E₁ := by
  unfold disjoinSeq
  rw [Fintype.card_congr σ.symm]
  exact disjoinSeqAux_equiv _ σ hσ

end Reindex

end Hironaka.Sequence
