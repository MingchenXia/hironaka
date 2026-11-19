import Hironaka.Geometry.ProjectiveProjectionMap
import Hironaka.Geometry.ProjStructureMap

/-!
# Actual chart cover and coefficient triangle for the relevant native Proj map
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open TopologicalSpace

namespace Hironaka.Geometry.ProjectiveProjection.General.Morph

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)
  (hf : ∀ p : ProjectiveSpectrum ℬ, ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ p.asHomogeneousIdeal.comap f)

include hf in
/-- The actual original homogeneous target charts induce a genuine affine source cover. -/
@[simps! I₀ X f]
def mapOpenCover : (Proj ℬ).OpenCover :=
  Scheme.Cover.mkOfCovers (Proj.affineOpenCover 𝒜).I₀
    (fun s => Spec (.of (Away ℬ (f s.2))))
    (fun s => Proj.awayι ℬ (f s.2) (f.map_mem s.2.2) s.1.2) (by
      intro p
      obtain ⟨s, a, ha⟩ := (Proj.affineOpenCover 𝒜).openCover.exists_eq (Point.comap f hf p)
      have hp : Point.comap f hf p ∈ Proj.basicOpen 𝒜 (s.2 : A) := by
        rw [← Proj.opensRange_awayι 𝒜 (s.2 : A) s.2.2 s.1.2]
        exact ⟨a, ha⟩
      refine ⟨s, ?_⟩
      change p ∈ (Proj.awayι ℬ (f s.2) (f.map_mem s.2.2) s.1.2).opensRange
      rw [Proj.opensRange_awayι]
      exact hp)

/-- The actual away maps form actual Cartesian scheme squares. -/
theorem isPullback_awayMap {d : ℕ} {s : A} (hd : 0 < d) (hs : s ∈ 𝒜 d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Proj.awayι ℬ (f s) (f.map_mem hs) hd) (Proj.awayι 𝒜 s hs hd) (map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact awayι_comp_map f hf hd s hs
  · simp only [Proj.opensRange_awayι, map_preimage_basicOpen]

/-- The literal homogeneous map with an explicitly identified original denominator
has the same exact native structure triangle. -/
theorem awayι_comp_map_of_eq {d : ℕ} {s : A} {t : B}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) (ht : t ∈ ℬ d) (heq : f s = t)
    (hmon : Submonoid.powers s ≤ (Submonoid.powers t).comap f) :
    Proj.awayι ℬ t ht hd ≫ map f hf =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f hmon)) ≫ Proj.awayι 𝒜 s hs hd := by
  subst t
  exact awayι_comp_map f hf hd s hs

/-- The actual original denominator comparison gives an actual Cartesian square. -/
theorem isPullback_awayMap_of_eq {d : ℕ} {s : A} {t : B}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) (ht : t ∈ ℬ d) (heq : f s = t)
    (hmon : Submonoid.powers s ≤ (Submonoid.powers t).comap f) :
    IsPullback (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f hmon)))
      (Proj.awayι ℬ t ht hd) (Proj.awayι 𝒜 s hs hd) (map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact awayι_comp_map_of_eq f hf hd hs ht heq hmon
  · simp only [Proj.opensRange_awayι, map_preimage_basicOpen, heq]

/-- The actual relevant Proj map preserves its original degree-zero coefficient maps. -/
theorem map_toSpecZero : map f hf ≫ Proj.toSpecZero 𝒜 =
    Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (ProjStructureMap.degreeZeroMap f)) := by
  refine (mapOpenCover f hf).hom_ext _ _ fun s => ?_
  simp only [mapOpenCover_f, awayι_comp_map_assoc f hf s.1.2 _ s.2.2,
    Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (ProjStructureMap.awayMap_comp_fromZero f s.2)

/-- Compatibility of the actual degree-zero coefficient maps gives the original base triangle. -/
theorem map_toSpec_base {R : Type u} [CommRing R]
    (α : R →+* 𝒜 0) (β : R →+* ℬ 0)
    (h : (ProjStructureMap.degreeZeroMap f).comp α = β) :
    map f hf ≫ (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom α)) =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom β) := by
  rw [← Category.assoc, map_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom h

end Hironaka.Geometry.ProjectiveProjection.General.Morph
