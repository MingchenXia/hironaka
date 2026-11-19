import Hironaka.Geometry.ProjectiveProjectionMapFunctoriality

/-!
# Actual relative naturality for the SAME original partially defined ambient projective map
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveProjection.General.Morph

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B C D σ τ υ ω : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C] [SetLike ω D] [AddSubgroupClass ω D]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → υ} {𝒟 : ℕ → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒟]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (g' : ℬ →+*ᵍ 𝒟)
  (hg : ∀ p : ProjectiveSpectrum 𝒞, ¬ irrelevant ℬ ≤ p.asHomogeneousIdeal.comap g)
  (hg' : ∀ p : ProjectiveSpectrum 𝒟, ¬ irrelevant ℬ ≤ p.asHomogeneousIdeal.comap g')
  (hf : ∀ p : ProjectiveSpectrum 𝒞, ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap (g.comp f))
  (h : Proj 𝒟 ⟶ Proj 𝒞) (H : h ≫ map g hg = map g' hg')

include hg hg' hf H

/-- The entire actual original ambient scheme triangle internally produces relevance of the SAME original new composite; no relevance of the ambient partial f is assumed. -/
theorem relevant_of_ambient_triangle (p : ProjectiveSpectrum 𝒟) :
    ¬ irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap (g'.comp f) := by
  have he := congrArg (fun m : Proj 𝒟 ⟶ Proj ℬ => (m p).asHomogeneousIdeal) H
  change (h p).asHomogeneousIdeal.comap g = p.asHomogeneousIdeal.comap g' at he
  change ¬ irrelevant 𝒜 ≤ (p.asHomogeneousIdeal.comap g').comap f
  rw [← he]
  exact hf (h p)

/-- The SAME actual entire original projective scheme morphisms commute under an actual entire original ambient triangle, even when f itself does NOT globally induce an ambient scheme map. -/
theorem map_naturality :
    map (g'.comp f) (relevant_of_ambient_triangle f g g' hg hg' hf h H) = h ≫ map (g.comp f) hf := by
  let hf' := relevant_of_ambient_triangle f g g' hg hg' hf h H
  refine (mapOpenCover (g'.comp f) hf').hom_ext _ _ fun s => ?_
  change (Proj.affineOpenCover 𝒜).I₀ at s
  simp only [mapOpenCover_f, GradedRingHom.comp_apply]
  let ac := Proj.awayι 𝒞 (g (f s.2)) (g.map_mem (f.map_mem s.2.2)) s.1.2
  let ad := Proj.awayι 𝒟 (g' (f s.2)) (g'.map_mem (f.map_mem s.2.2)) s.1.2
  let b := Proj.awayι ℬ (f s.2) (f.map_mem s.2.2) s.1.2
  let a := Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2
  let β := Spec.map (CommRingCat.ofHom (Away.map g (f s.2)))
  let β' := Spec.map (CommRingCat.ofHom (Away.map g' (f s.2)))
  have hc : β' ≫ b = (ad ≫ h) ≫ map g hg := by
    rw [Category.assoc, H]
    exact (awayι_comp_map g' hg' s.1.2 (f s.2) (f.map_mem s.2.2)).symm
  let S := isPullback_awayMap g hg s.1.2 (f.map_mem s.2.2)
  let t := S.lift β' (ad ≫ h) hc
  have ht₁ : t ≫ β = β' := S.lift_fst β' (ad ≫ h) hc
  have ht₂ : t ≫ ac = ad ≫ h := S.lift_snd β' (ad ≫ h) hc
  change ad ≫ map (g'.comp f) hf' = ad ≫ h ≫ map (g.comp f) hf
  symm
  calc
    ad ≫ h ≫ map (g.comp f) hf = t ≫ ac ≫ map (g.comp f) hf := by
      rw [← Category.assoc, ← ht₂, Category.assoc]
    _ = t ≫ Spec.map (CommRingCat.ofHom (Away.map (g.comp f) s.2)) ≫ a := by
      exact congrArg (fun m => t ≫ m) (awayι_comp_map (g.comp f) hf s.1.2 s.2 s.2.2)
    _ = (t ≫ β) ≫ Spec.map (CommRingCat.ofHom (Away.map f s.2)) ≫ a := by
      simp only [Away.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, β]
    _ = β' ≫ Spec.map (CommRingCat.ofHom (Away.map f s.2)) ≫ a := by rw [ht₁]
    _ = ad ≫ map (g'.comp f) hf' := by
      simpa only [Away.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, GradedRingHom.comp_apply, β', ad, a] using
        (awayι_comp_map (g'.comp f) hf' s.1.2 s.2 s.2.2).symm

end Hironaka.Geometry.ProjectiveProjection.General.Morph
