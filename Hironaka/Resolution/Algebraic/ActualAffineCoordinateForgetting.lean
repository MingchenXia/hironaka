import Hironaka.Resolution.Algebraic.ActualGlobalSeparationBlowupFunctoriality

/-!
# Actual coordinate forgetting for genuine smooth padded comparisons

Source-first proof: `actual-affine-coordinate-forgetting-20261102.tex`.
Actual coordinate blocks and universal affine projections derive smoothness,
surjectivity and BOTH original projection/zero-section identities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualAffineCoordinateForgetting

noncomputable section
open ActualAffineSpaceSumDecomposition ActualCommonPaddedEnvelopeGeometry
variable {σ τ : Type u}

def coordinateBlockEquiv (i : σ → τ) (hi : Function.Injective i) :
    σ ⊕ {t : τ // t ∉ Set.range i} ≃ τ := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective i hi) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range i))

theorem coordinateBlockEquiv_inl (i : σ → τ) (hi : Function.Injective i) (s : σ) :
    coordinateBlockEquiv i hi (Sum.inl s) = i s := rfl

private instance reindex_equiv_isIso (e : σ ≃ τ) (X : Scheme.{u}) : IsIso (AffineSpace.reindex e X) := by
  refine ⟨⟨AffineSpace.reindex e.symm X, ?_, ?_⟩⟩
  · apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.reindex_over, Category.id_comp]
    · intro s
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        Equiv.apply_symm_apply, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  · apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.reindex_over, Category.id_comp]
    · intro s
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        Equiv.symm_apply_apply, Scheme.Hom.id_appTop, CommRingCat.id_apply]

theorem reindex_injective_factor (i : σ → τ) (hi : Function.Injective i) (X : Scheme.{u}) :
    AffineSpace.reindex i X = AffineSpace.reindex (coordinateBlockEquiv i hi) X ≫
      AffineSpace.reindex (Sum.inl : σ → σ ⊕ {t : τ // t ∉ Set.range i}) X := by
  have hcomp : TypeCat.ofHom (Sum.inl : σ → σ ⊕ {t : τ // t ∉ Set.range i}) ≫
      TypeCat.ofHom (coordinateBlockEquiv i hi) = TypeCat.ofHom i := by
    ext s
    exact coordinateBlockEquiv_inl i hi s
  have h := AffineSpace.reindex_comp
    (TypeCat.ofHom (Sum.inl : σ → σ ⊕ {t : τ // t ∉ Set.range i}))
    (TypeCat.ofHom (coordinateBlockEquiv i hi)) X
  rw [hcomp] at h
  exact h

theorem reindex_smooth_of_injective [Finite τ] (i : σ → τ) (hi : Function.Injective i) (X : Scheme.{u}) :
    Smooth (AffineSpace.reindex i X) := by
  let D := {t : τ // t ∉ Set.range i}
  have hd := affine_projection_relativeDimension D X
  have : Smooth (AffineSpace D X ↘ X) := SmoothOfRelativeDimension.smooth (Nat.card D) _
  have : Smooth (AffineSpace.map σ (AffineSpace D X ↘ X)) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := σ) (AffineSpace D X ↘ X)) inferInstance
  rw [reindex_injective_factor i hi X, ← sumTowerIso_first σ D X]
  infer_instance

theorem reindex_surjective_of_injective (i : σ → τ) (hi : Function.Injective i) (X : Scheme.{u}) :
    Surjective (AffineSpace.reindex i X) := by
  let D := {t : τ // t ∉ Set.range i}
  have : Surjective (AffineSpace.map σ (AffineSpace D X ↘ X)) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := σ) (AffineSpace D X ↘ X)) inferInstance
  rw [reindex_injective_factor i hi X, ← sumTowerIso_first σ D X]
  infer_instance

def coordinateMap {X Y : Scheme.{u}} (i : σ → τ) (f : Y ⟶ X) :
    AffineSpace τ Y ⟶ AffineSpace σ X := AffineSpace.reindex i Y ≫ AffineSpace.map σ f

theorem coordinateMap_over {X Y : Scheme.{u}} (i : σ → τ) (f : Y ⟶ X) :
    coordinateMap i f ≫ (AffineSpace σ X ↘ X) = (AffineSpace τ Y ↘ Y) ≫ f := by
  rw [coordinateMap, Category.assoc, AffineSpace.map_over, ← Category.assoc, AffineSpace.reindex_over]

theorem coordinateMap_smooth [Finite τ] {X Y : Scheme.{u}} (i : σ → τ) (hi : Function.Injective i)
    (f : Y ⟶ X) [Smooth f] : Smooth (coordinateMap i f) := by
  have := reindex_smooth_of_injective i hi Y
  have : Smooth (AffineSpace.map σ f) := property_of_isPullback _ (AffineSpace.isPullback_map (n := σ) f) inferInstance
  dsimp only [coordinateMap]
  infer_instance

theorem coordinateMap_surjective {X Y : Scheme.{u}} (i : σ → τ) (hi : Function.Injective i)
    (f : Y ⟶ X) [Surjective f] : Surjective (coordinateMap i f) := by
  have := reindex_surjective_of_injective i hi Y
  have : Surjective (AffineSpace.map σ f) := property_of_isPullback _ (AffineSpace.isPullback_map (n := σ) f) inferInstance
  dsimp only [coordinateMap]
  infer_instance

theorem coordinateMap_zero {X Y : Scheme.{u}} (i : σ → τ) (f : Y ⟶ X) :
    AffineSpace.homOfVector (𝟙 Y) (fun _ : τ => 0) ≫ coordinateMap i f =
      f ≫ AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0) := by
  apply AffineSpace.hom_ext
  · simp only [coordinateMap, Category.assoc, AffineSpace.map_over,
      AffineSpace.homOfVector_over, Category.comp_id]
    rw [← Category.assoc (AffineSpace.reindex i Y), AffineSpace.reindex_over,
      ← Category.assoc, AffineSpace.homOfVector_over, Category.id_comp]
  · intro s
    simp only [coordinateMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, AffineSpace.reindex_appTop_coord,
      AffineSpace.homOfVector_appTop_coord, map_zero]

end
end Hironaka.Resolution.Algebraic.ActualAffineCoordinateForgetting
