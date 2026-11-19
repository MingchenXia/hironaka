import Hironaka.Geometry.ProjectiveProjectionStructure

/-!
# Entire actual functoriality for the SAME original prime-relevant projective projection maps
-/

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveProjection.General.Morph

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B C σ τ υ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → υ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
  (hf : ∀ p : ProjectiveSpectrum ℬ, ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap f)
  (hg : ∀ p : ProjectiveSpectrum 𝒞, ¬ irrelevant ℬ ≤ p.asHomogeneousIdeal.comap g)

include hf hg in
/-- The same actual original prime-relevance predicates internally produce relevance of the SAME entire graded composite. -/
theorem relevant_comp (p : ProjectiveSpectrum 𝒞) :
    ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap (g.comp f) :=
  hf (Point.comap g hg p)

/-- The SAME actual original prime-relevant projective scheme morphisms compose literally on the ENTIRE original schemes. -/
theorem map_comp : map (g.comp f) (relevant_comp f g hf hg) = map g hg ≫ map f hf := by
  refine (mapOpenCover (g.comp f) (relevant_comp f g hf hg)).hom_ext _ _ fun s => ?_
  simp only [mapOpenCover_f, awayι_comp_map (g.comp f) _ s.1.2 _ s.2.2]
  simp only [GradedRingHom.comp_apply]
  rw [← Category.assoc, awayι_comp_map g hg s.1.2 (f s.2) (f.map_mem s.2.2),
    Category.assoc, awayι_comp_map f hf s.1.2 s.2 s.2.2]
  simp only [Away.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- Native original irrelevant containment internally implies the SAME actual prime-relevance condition. -/
theorem relevant_of_irrelevant_le
    (hf' : irrelevant ℬ ≤ (irrelevant 𝒜).map f) (p : ProjectiveSpectrum ℬ) :
    ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap f := by
  intro h
  exact p.not_irrelevant_le (hf'.trans (HomogeneousIdeal.map_le_of_le_comap _ h))

/-- The weakened true relevance construction retains the exact SAME native whole Proj scheme map whenever the native original hypothesis holds. -/
theorem map_eq_native (hf' : irrelevant ℬ ≤ (irrelevant 𝒜).map f) :
    map f (relevant_of_irrelevant_le f hf') = Proj.map f hf' := rfl

end Hironaka.Geometry.ProjectiveProjection.General.Morph
