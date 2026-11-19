import Hironaka.Geometry.ProjectiveProjectionMapNaturality

/-!
# Entire actual partial projection scheme maps retain original graded coefficient squares
-/

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal

namespace Hironaka.Geometry.ProjectiveProjection.General.Morph

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Entire original graded-map equality gives literal equality of the SAME actual whole relevant scheme maps, independently of the relevance proof. -/
theorem map_congr {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f₁ f₂ : 𝒜 →+*ᵍ ℬ)
    (hf₁ : ∀ p : ProjectiveSpectrum ℬ, ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap f₁)
    (hf₂ : ∀ p : ProjectiveSpectrum ℬ, ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap f₂)
    (heq : f₁ = f₂) : map f₁ hf₁ = map f₂ hf₂ := by
  subst f₂
  rfl

variable {A B C A' B' C' σ τ υ σ' τ' υ' : Type u}
  [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [CommRing B'] [CommRing C']
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C] [SetLike σ' A'] [AddSubgroupClass σ' A']
  [SetLike τ' B'] [AddSubgroupClass τ' B'] [SetLike υ' C'] [AddSubgroupClass υ' C']
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → υ} {𝒜' : ℕ → σ'} {ℬ' : ℕ → τ'} {𝒞' : ℕ → υ'}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒜'] [GradedRing ℬ'] [GradedRing 𝒞']
  (f : 𝒜 →+*ᵍ ℬ) (f' : 𝒜' →+*ᵍ ℬ') (a : 𝒜 →+*ᵍ 𝒜') (b : ℬ →+*ᵍ ℬ')
  (g : ℬ →+*ᵍ 𝒞) (g' : ℬ' →+*ᵍ 𝒞')
  (ha : ∀ p : ProjectiveSpectrum 𝒜', ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap a)
  (hb : ∀ p : ProjectiveSpectrum ℬ', ¬ irrelevant ℬ ≤ p.asHomogeneousIdeal.comap b)
  (hg : ∀ p : ProjectiveSpectrum 𝒞, ¬ irrelevant ℬ ≤ p.asHomogeneousIdeal.comap g)
  (hg' : ∀ p : ProjectiveSpectrum 𝒞', ¬ irrelevant ℬ' ≤ p.asHomogeneousIdeal.comap g')
  (hf : ∀ p : ProjectiveSpectrum 𝒞, ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap (g.comp f))
  (hf' : ∀ p : ProjectiveSpectrum 𝒞', ¬ irrelevant 𝒜' ≤ p.asHomogeneousIdeal.comap (g'.comp f'))
  (h : Proj 𝒞' ⟶ Proj 𝒞)
  (H : h ≫ map g hg = map (g'.comp b) (relevant_comp b g' hb hg'))
  (hsquare : b.comp f = f'.comp a)

include H hsquare

/-- The SAME actual entire original source/ambient triangle and original WHOLE graded coefficient square give the literal whole projection scheme-map coefficient square. -/
theorem map_coefficient_square :
    map (g'.comp f') hf' ≫ map a ha = h ≫ map (g.comp f) hf := by
  let hi := relevant_of_ambient_triangle f g (g'.comp b) hg (relevant_comp b g' hb hg') hf h H
  have N := map_naturality f g (g'.comp b) hg (relevant_comp b g' hb hg') hf h H
  have he : (g'.comp b).comp f = (g'.comp f').comp a := by
    apply DFunLike.ext
    intro x
    exact congrArg (fun y => g' y) (DFunLike.congr_fun hsquare x)
  calc
    map (g'.comp f') hf' ≫ map a ha = map ((g'.comp f').comp a) (relevant_comp a (g'.comp f') ha hf') :=
      (map_comp a (g'.comp f') ha hf').symm
    _ = map ((g'.comp b).comp f) hi := map_congr _ _ _ hi he.symm
    _ = h ≫ map (g.comp f) hf := N

end Hironaka.Geometry.ProjectiveProjection.General.Morph
