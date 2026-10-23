/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ClosedFibreCanonicalNormalization

/-! # The actual original native inclusions between finite point-set normalizations -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.CanonicalNormalization

universe u

open StableModification.CurvesField StableModification.CurvesField.Genus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from T))]
  {A B : Set T} [Finite A] [Finite B] (h : A ⊆ B)

/-- The actual original inclusion is produced by the native normalization universal property. -/
def normalizationPointsIncl : normalizationPoints A ⟶ normalizationPoints B :=
  (pointsMap T A).normalizationDesc
    (pointsIncl h ≫ (pointsMap T B).toNormalization) (pointsMap T B).fromNormalization (by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, pointsIncl_pointsMap])

@[reassoc (attr := simp)]
theorem normalizationPointsIncl_fromNormalization :
    normalizationPointsIncl h ≫ normalizationPointsMap B = normalizationPointsMap A :=
  Scheme.Hom.normalizationDesc_comp _ _ _ _

@[reassoc (attr := simp)]
theorem toNormalization_normalizationPointsIncl :
    (pointsMap T A).toNormalization ≫ normalizationPointsIncl h =
      pointsIncl h ≫ (pointsMap T B).toNormalization :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

instance : IsIntegralHom (normalizationPointsIncl h) := by
  unfold normalizationPointsIncl
  infer_instance

omit [IsAffineHom (pullback.diagonal (terminal.from T))] [Finite A] [Finite B] in
/-- The SAME original two point-scheme inclusions are complementary. -/
theorem isCompl_pointsIncl_complement :
    IsCompl (pointsIncl h).opensRange
      (pointsIncl (Set.sdiff_subset : B \ A ⊆ B)).opensRange := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h₁ := pointsMap_mem a
    have h₂ := pointsMap_mem b
    rw [← pointsIncl_pointsMap h, Scheme.Hom.comp_apply] at h₁
    rw [← pointsIncl_pointsMap (Set.sdiff_subset : B \ A ⊆ B),
      Scheme.Hom.comp_apply, hb] at h₂
    exact h₂.2 h₁
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    by_cases hz : pointsMap T B z ∈ A
    · exact Opens.mem_sup.mpr (Or.inl (mem_range_pointsIncl h z hz))
    · exact Opens.mem_sup.mpr (Or.inr (mem_range_pointsIncl Set.sdiff_subset z ⟨pointsMap_mem z, hz⟩))

instance isOpenImmersion_normalizationPointsIncl : IsOpenImmersion (normalizationPointsIncl h) := by
  have : Finite (B \ A : Set T) :=  Finite.of_injective
    (fun x : (B \ A : Set T) => (⟨x.1, x.2.1⟩ : B))
    (fun _ _ e => Subtype.ext (congrArg (fun z : B => z.1) e))
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_pointsIncl_complement h)
  have hA := pointsIncl_pointsMap h
  have hD := pointsIncl_pointsMap (Set.sdiff_subset : B \ A ⊆ B)
  have aux {P Q U V : Scheme.{u}} (g : P ⟶ Q) (iU : U ⟶ P) (iV : V ⟶ P)
      (gU : U ⟶ Q) (gV : V ⟶ Q) (hU : iU ≫ g = gU) (hV : iV ≫ g = gV)
      (ec : IsColimit (BinaryCofan.mk iU iV))
      [QuasiCompact g] [QuasiSeparated g] [QuasiCompact iU] [QuasiSeparated iU]
      [QuasiCompact iV] [QuasiSeparated iV] [QuasiCompact gU] [QuasiSeparated gU]
      [QuasiCompact gV] [QuasiSeparated gV] :
      IsOpenImmersion (gU.normalizationDesc (iU ≫ g.toNormalization) g.fromNormalization (by
        rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hU])) := by
    subst hU hV
    have he : (iU ≫ g).normalizationDesc (iU ≫ g.toNormalization) g.fromNormalization (by simp) =
        coprod.inl ≫ (g.normalizationCoprodIso ec).hom := by
      simp [Scheme.Hom.normalizationCoprodIso]
    rw [he]
    infer_instance
  exact aux (pointsMap T B) (pointsIncl h) (pointsIncl Set.sdiff_subset)
    (pointsMap T A) (pointsMap T (B \ A)) hA hD e

instance isFinite_normalizationPointsIncl : IsFinite (normalizationPointsIncl h) :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

instance isClosedImmersion_normalizationPointsIncl : IsClosedImmersion (normalizationPointsIncl h) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end DeJongAlterations.Geometry.CanonicalNormalization
