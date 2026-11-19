import Hironaka.Resolution.Algebraic.ActualCommonPaddedEnvelopeGeometry

/-!
# Actual affine coordinate blocks and the genuine common padded product

Source-first proof: `actual-affine-space-sum-decomposition-20261102.tex`.
The isomorphisms are constructed from original coordinates and base maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualAffineSpaceSumDecomposition

noncomputable section
variable (V₁ V₂ : Type u) (X : Scheme.{u})

private def toTower : AffineSpace (V₁ ⊕ V₂) X ⟶ AffineSpace V₁ (AffineSpace V₂ X) :=
  AffineSpace.homOfVector (AffineSpace.reindex Sum.inr X)
    (fun i => AffineSpace.coord X (Sum.inl i))

private def fromTower : AffineSpace V₁ (AffineSpace V₂ X) ⟶ AffineSpace (V₁ ⊕ V₂) X :=
  AffineSpace.homOfVector ((AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X) ≫ (AffineSpace V₂ X ↘ X))
    (Sum.elim (AffineSpace.coord (AffineSpace V₂ X))
      (fun j => (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X).appTop (AffineSpace.coord X j)))

private theorem toTower_over :
    toTower V₁ V₂ X ≫ (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X) =
      AffineSpace.reindex Sum.inr X := AffineSpace.homOfVector_over _ _

private theorem fromTower_over : fromTower V₁ V₂ X ≫ (AffineSpace (V₁ ⊕ V₂) X ↘ X) =
    (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X) ≫ (AffineSpace V₂ X ↘ X) :=
  AffineSpace.homOfVector_over _ _

private theorem toTower_coord (i : V₁) :
    (toTower V₁ V₂ X).appTop (AffineSpace.coord (AffineSpace V₂ X) i) =
      AffineSpace.coord X (Sum.inl i) := AffineSpace.homOfVector_appTop_coord _ _ _

private theorem fromTower_coord (i : V₁ ⊕ V₂) :
    (fromTower V₁ V₂ X).appTop (AffineSpace.coord X i) =
      Sum.elim (AffineSpace.coord (AffineSpace V₂ X))
        (fun j => (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X).appTop (AffineSpace.coord X j)) i :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem fromTower_second :
    fromTower V₁ V₂ X ≫ AffineSpace.reindex Sum.inr X =
      (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X) := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc,AffineSpace.reindex_over,fromTower_over]
  · intro j
    simp only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,AffineSpace.reindex_appTop_coord,
      fromTower_coord,Sum.elim_inr]

/-- Genuine coordinate-block isomorphism, retaining both actual original projections. -/
def sumTowerIso : AffineSpace (V₁ ⊕ V₂) X ≅ AffineSpace V₁ (AffineSpace V₂ X) where
  hom := toTower V₁ V₂ X
  inv := fromTower V₁ V₂ X
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc,fromTower_over,← Category.assoc,toTower_over,AffineSpace.reindex_over,
        Category.id_comp]
    · intro i
      cases i with
      | inl i =>
        simp only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,fromTower_coord,Sum.elim_inl,
          toTower_coord,Scheme.Hom.id_appTop,CommRingCat.id_apply]
      | inr j =>
        simp only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,fromTower_coord,Sum.elim_inr,
          Scheme.Hom.id_appTop,CommRingCat.id_apply]
        rw [← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop,toTower_over,AffineSpace.reindex_appTop_coord]
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc,toTower_over,fromTower_second,Category.id_comp]
    · intro i
      simp only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,toTower_coord,fromTower_coord,
        Sum.elim_inl,Scheme.Hom.id_appTop,CommRingCat.id_apply]

/-- The second original block projection is the actual relative product projection. -/
theorem sumTowerIso_second :
    (sumTowerIso V₁ V₂ X).hom ≫ (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X) =
      AffineSpace.reindex Sum.inr X := toTower_over V₁ V₂ X

/-- The first original block projection is the actual other product projection. -/
theorem sumTowerIso_first :
    (sumTowerIso V₁ V₂ X).hom ≫ AffineSpace.map V₁ (AffineSpace V₂ X ↘ X) =
      AffineSpace.reindex Sum.inl X := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc,AffineSpace.map_over,← Category.assoc,sumTowerIso_second,
      AffineSpace.reindex_over,AffineSpace.reindex_over]
  · intro i
    simp only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,AffineSpace.map_appTop_coord,
      AffineSpace.reindex_appTop_coord]
    exact toTower_coord V₁ V₂ X i

variable (D : Type u)

private instance map_sumTower_isIso : IsIso (AffineSpace.map D (sumTowerIso V₁ V₂ X).hom) := by
  have he := AffineSpace.map_comp (n := D) (sumTowerIso V₁ V₂ X).hom (sumTowerIso V₁ V₂ X).inv
  have he' := AffineSpace.map_comp (n := D) (sumTowerIso V₁ V₂ X).inv (sumTowerIso V₁ V₂ X).hom
  refine ⟨⟨AffineSpace.map D (sumTowerIso V₁ V₂ X).inv,?_,?_⟩⟩
  · rw [← he,Iso.hom_inv_id,AffineSpace.map_id]
  · rw [← he',Iso.inv_hom_id,AffineSpace.map_id]

/-- Three actual original coordinate blocks form the SAME genuine common padded piece. -/
def commonSumIso : AffineSpace (D ⊕ (V₁ ⊕ V₂)) X ≅
    ActualCommonPaddedEnvelopeGeometry.commonSpace V₁ V₂ D X :=
  sumTowerIso D (V₁ ⊕ V₂) X ≪≫ asIso (AffineSpace.map D (sumTowerIso V₁ V₂ X).hom)

/-- This actual coordinate isomorphism lies over the SAME original common projection. -/
theorem commonSumIso_over : (commonSumIso V₁ V₂ X D).hom ≫
    (ActualCommonPaddedEnvelopeGeometry.commonToFirst V₁ V₂ D X ≫ (AffineSpace V₁ X ↘ X)) =
      (AffineSpace (D ⊕ (V₁ ⊕ V₂)) X ↘ X) := by
  rw [commonSumIso,Iso.trans_hom,asIso_hom,ActualCommonPaddedEnvelopeGeometry.commonToFirst]
  simp only [Category.assoc,← Category.assoc (AffineSpace.map D _),AffineSpace.map_over]
  rw [← Category.assoc,sumTowerIso_second]
  rw [← Category.assoc (sumTowerIso V₁ V₂ X).hom,sumTowerIso_second,
    AffineSpace.reindex_over,AffineSpace.reindex_over]

end
end Hironaka.Resolution.Algebraic.ActualAffineSpaceSumDecomposition
