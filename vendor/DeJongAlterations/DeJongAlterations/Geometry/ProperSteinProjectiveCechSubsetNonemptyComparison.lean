/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubset
import Mathlib.LinearAlgebra.Pi

/-! # Genuine normalized-complex comparisons require only nonempty intersections

No affine or comparison assertion is required for the empty original subset.
The original maps and original restriction squares are retained throughout.
-/
open CategoryTheory
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech.SubsetNonemptyComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R ι : Type u} [CommRing R] [LinearOrder ι]
  (F G : Finset ι ⥤ ModuleCat.{u} R)
  (E : ∀ (S : Finset ι) (_hS : S.Nonempty), F.obj S ≅ G.obj S)

/-- Positive original cardinal pieces use ONLY the actual nonempty original frames. -/
def cardinalEquiv (n : ℕ) (hn : 0<n) :
    subsetCechCardPiece F n ≃ₗ[R] subsetCechCardPiece G n :=
  subsetCechCardProductEquiv F n ≪≫ₗ
    (LinearEquiv.piCongrRight fun S =>
      (E S.val (Finset.card_pos.mp (S.property.symm ▸ hn))).toLinearEquiv) ≪≫ₗ
    (subsetCechCardProductEquiv G n).symm

omit [LinearOrder ι] in
/-- EVERY original coefficient in the actual positive degree uses the specified original frame. -/
theorem cardinalEquiv_apply_of_card (n : ℕ) (hn : 0<n)
    (x : subsetCechCardPiece F n) (S : Finset ι) (hS : S.card=n) :
    (cardinalEquiv F G E n hn x).val S =
      (E S (Finset.card_pos.mp (hS.symm ▸ hn))).hom (x.val S) := by
  classical
  change (if h : S.card=n then _ else 0) = _
  rw [dif_pos hS]
  rfl

variable (hE : ∀ (S T : Finset ι) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T),
  F.map (homOfLE hST) ≫ (E T hT).hom = (E S hS).hom ≫ G.map (homOfLE hST))
include hE

/-- The ACTUAL signed original differentials commute using ONLY nonempty original restrictions. -/
theorem cardinalEquiv_differential (n : ℕ) (x : subsetCechCardPiece F (n+1)) :
    cardinalEquiv F G E (n+2) (by omega) (subsetCechCardDifferential F (n+1) x) =
      subsetCechCardDifferential G (n+1) (cardinalEquiv F G E (n+1) (by omega) x) := by
  apply Subtype.ext
  funext S
  by_cases hS : S.card=n+2
  · rw [cardinalEquiv_apply_of_card F G E (n+2) (by omega) _ S hS]
    change (E S _).hom (∑ i ∈ S, subsetCechSign S i •
      F.map (homOfLE (Finset.erase_subset i S)) (x.val (S.erase i))) =
      ∑ i ∈ S, subsetCechSign S i • G.map (homOfLE (Finset.erase_subset i S))
        ((cardinalEquiv F G E (n+1) (by omega) x).val (S.erase i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul]
    have he : (S.erase i).card=n+1 := by
      rw [Finset.card_erase_of_mem hi, hS]
      omega
    rw [cardinalEquiv_apply_of_card F G E (n+1) (by omega) x (S.erase i) he]
    congr 1
    exact ConcreteCategory.congr_hom (hE (S.erase i) S _ _ (Finset.erase_subset i S))
      (x.val (S.erase i))
  · rw [(cardinalEquiv F G E (n+2) (by omega)
      (subsetCechCardDifferential F (n+1) x)).property S hS,
      (subsetCechCardDifferential G (n+1)
        (cardinalEquiv F G E (n+1) (by omega) x)).property S hS]

/-- The WHOLE native normalized complexes retain the SAME nonempty original frames. -/
def complexIso : subsetCechComplex F ≅ subsetCechComplex G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cardinalEquiv F G E (n+1) (by omega)).toModuleIso) (by
      intro n m h
      have hm : n+1=m := h
      subst m
      simp only [subsetCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change subsetCechCardDifferential G (n+1) (cardinalEquiv F G E (n+1) (by omega) x) =
        cardinalEquiv F G E (n+1+1) (by omega) (subsetCechCardDifferential F (n+1) x)
      exact (cardinalEquiv_differential F G E hE n x).symm)

end DeJongAlterations.Geometry.ProperSteinProjectiveCech.SubsetNonemptyComparison
