import Hironaka.Geometry.ProjectiveSecantLine

/-!
# Actual native projective points in the range of an original graded surjection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Whole original kernel containment internally produces an actual native source projective point of the literal original graded surjection. -/
theorem point_mem_range_projMap_of_ker_le
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (P : ProjectiveSpectrum 𝒜) (hker : RingHom.ker f.toRingHom ≤ P.asHomogeneousIdeal.toIdeal) :
    P ∈ Set.range (Proj.map f hf) := by
  let J := P.asHomogeneousIdeal.map f
  let : P.asHomogeneousIdeal.toIdeal.IsPrime := P.isPrime
  have hc : J.comap f = P.asHomogeneousIdeal := by
    apply HomogeneousIdeal.ext
    change Ideal.comap f.toRingHom (Ideal.map f.toRingHom P.asHomogeneousIdeal.toIdeal) = _
    exact (Ideal.comap_map_of_surjective f.toRingHom hsurj P.asHomogeneousIdeal.toIdeal).trans
      (sup_eq_left.mpr hker)
  have hJ : J.toIdeal.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  have hirr : ¬ HomogeneousIdeal.irrelevant ℬ ≤ J := by
    intro h
    apply P.not_irrelevant_le
    rw [HomogeneousIdeal.irrelevant_le]
    intro d hd a ha
    have hm : f a ∈ J := h (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hd (f.map_mem ha))
    change a ∈ J.comap f at hm
    rwa [hc] at hm
  refine ⟨⟨J, hJ, hirr⟩, ?_⟩
  exact ProjectiveSpectrum.ext hc

end Hironaka.Geometry.ProjectiveSecant
