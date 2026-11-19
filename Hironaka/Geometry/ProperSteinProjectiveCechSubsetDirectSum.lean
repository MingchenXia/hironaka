/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechSubset
import Hironaka.Geometry.ProperSteinProjectiveCechReesCoefficients
import Hironaka.Geometry.ProperSteinProjectiveCechDirectSumHomology

/-! # Literal original finite subset complexes and genuine degree direct sums

This constructs every original differential comparison. No affine, grading,
cohomology-finiteness or homology-comparison certificate is an input.
-/
open CategoryTheory
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.SubsetDirectSum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R ι : Type u} [CommRing R] [LinearOrder ι]
  (F : ℕ → Finset ι ⥤ ModuleCat.{u} R)

/-- The LITERAL direct sum of the original diagrams and their actual maps. -/
def diagram : Finset ι ⥤ ModuleCat.{u} R where
  obj S := ModuleCat.of R (⨁ d : ℕ, (F d).obj S)
  map h := ModuleCat.ofHom (DirectSum.lmap fun d => ((F d).map h).hom)
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    change ((F d).map (𝟙 S)) (x d) = x d
    rw [(F d).map_id S]
    rfl
  map_comp h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    change ((F d).map (h ≫ k)) (x d) = (F d).map k ((F d).map h (x d))
    rw [Functor.map_comp]
    rfl

variable [Fintype ι]

/-- The SAME actual cardinal piece decomposes into its original degree cardinal pieces. -/
def cardinalEquiv (n : ℕ) :
    subsetCechCardPiece (diagram F) n ≃ₗ[R] ⨁ d : ℕ, subsetCechCardPiece (F d) n :=
  subsetCechCardProductEquiv (diagram F) n ≪≫ₗ
    ReesCoefficients.finitePiDirectSumEquiv R {S : Finset ι // S.card = n}
      (fun S d => (F d).obj S.val) ≪≫ₗ
    DFinsupp.mapRange.linearEquiv (fun d => (subsetCechCardProductEquiv (F d) n).symm)

omit [LinearOrder ι] in
/-- EVERY original intersection coefficient is retained in its exact original degree. -/
theorem cardinalEquiv_apply (n : ℕ) (x : subsetCechCardPiece (diagram F) n)
    (d : ℕ) (S : Finset ι) :
    (cardinalEquiv F n x d).val S = (show ⨁ e : ℕ, (F e).obj S from x.val S) d := by
  classical
  by_cases h : S.card = n
  · change (if h' : S.card = n then _ else 0) = _
    rw [dif_pos h]
    rfl
  · rw [(cardinalEquiv F n x d).property S h, x.property S h]
    rfl

/-- The ACTUAL signed original differential retains EVERY original direct-sum degree. -/
theorem cardinalEquiv_differential (n : ℕ)
    (x : subsetCechCardPiece (diagram F) n) :
    cardinalEquiv F (n+1) (subsetCechCardDifferential (diagram F) n x) =
      DirectSum.lmap (fun d => subsetCechCardDifferential (F d) n) (cardinalEquiv F n x) := by
  apply DirectSum.ext
  intro d
  apply Subtype.ext
  funext S
  rw [cardinalEquiv_apply]
  change (∑ i ∈ S, subsetCechSign S i •
    (DirectSum.lmap fun e => ((F e).map (homOfLE (Finset.erase_subset i S))).hom)
      (x.val (S.erase i))) d =
    ∑ i ∈ S, subsetCechSign S i •
      (F d).map (homOfLE (Finset.erase_subset i S)) ((cardinalEquiv F n x d).val (S.erase i))
  simp only [DirectSum.sum_apply, DirectSum.smul_apply, DirectSum.lmap_apply, cardinalEquiv_apply]

section ComplexSum
variable (C : ℕ → CochainComplex (ModuleCat.{u} R) ℕ)

/-- The LITERAL direct-sum complex with the SAME actual coordinate differentials. -/
def complexSum : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (⨁ d : ℕ, (C d).X n))
    (fun n => ModuleCat.ofHom (DirectSum.lmap fun d => ((C d).d n (n+1)).hom)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DirectSum.ext
      intro d
      exact congrArg (fun q => q.hom (x d)) ((C d).d_comp_d n (n+1) (n+1+1)))

/-- EVERY differential, including all off-shape zero maps, retains the actual original degree. -/
theorem complexSum_d_apply (n m : ℕ) (x : ⨁ d : ℕ, (C d).X n) (d : ℕ) :
    (show ⨁ e : ℕ, (C e).X m from ((complexSum C).d n m).hom x) d =
      ((C d).d n m).hom (x d) := by
  by_cases h : n+1=m
  · subst m
    simp only [complexSum, CochainComplex.of_d, ModuleCat.hom_ofHom, DirectSum.lmap_apply]
  · rw [(complexSum C).shape n m h, (C d).shape n m h]
    rfl

/-- The actual native homology short complex retains its literal original direct-sum coordinates. -/
def shortComplexIso (n : ℕ) :
    (complexSum C).sc n ≅ DirectSumHomology.directSum (fun d => (C d).sc n) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    exact (complexSum_d_apply C _ _ x d).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    exact (complexSum_d_apply C _ _ x d).symm

/-- Genuine native homology of the actual whole direct-sum complex. -/
def complexSumHomologyIso (n : ℕ) :
    (complexSum C).homology n ≅ ModuleCat.of R (⨁ d : ℕ, (C d).homology n) :=
  (ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso (shortComplexIso C n) ≪≫
    DirectSumHomology.homologyIso (fun d => (C d).sc n)
end ComplexSum

/-- The WHOLE actual original subset complex is its genuine degree direct-sum complex. -/
def complexIso :
    subsetCechComplex (diagram F) ≅ complexSum (fun d => subsetCechComplex (F d)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cardinalEquiv F (n+1)).toModuleIso) (by
    intro n m h
    have hm : n+1=m := h
    subst m
    simp only [complexSum, subsetCechComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DirectSum.lmap (fun d => subsetCechCardDifferential (F d) (n+1))
      (cardinalEquiv F (n+1) x) =
        cardinalEquiv F (n+1+1) (subsetCechCardDifferential (diagram F) (n+1) x)
    exact (cardinalEquiv_differential F (n+1) x).symm)

/-- The ACTUAL original subset-complex homology is the direct sum of the original native homologies. -/
def homologyIso (n : ℕ) :
    (subsetCechComplex (diagram F)).homology n ≅
      ModuleCat.of R (⨁ d : ℕ, (subsetCechComplex (F d)).homology n) :=
  HomologicalComplex.homologyMapIso (complexIso F) n ≪≫
    complexSumHomologyIso (fun d => subsetCechComplex (F d)) n

end Hironaka.Geometry.ProperSteinProjectiveCech.SubsetDirectSum
