import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Naturality of the projective structure morphism

The native morphism induced by a graded ring homomorphism commutes with the
native structure morphisms to the spectra of the actual degree-zero rings.
-/

open AlgebraicGeometry CategoryTheory Graded HomogeneousLocalization

noncomputable section

universe u

namespace DeJongAlterations.Geometry.ProjStructureMap

variable {A B σ τ : Type u}
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Restrict a graded ring homomorphism to the actual degree-zero subrings. -/
abbrev degreeZeroMap (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 :=
  f.gradedZeroRingHom

set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous localization map preserves the actual degree-zero constants. -/
theorem awayMap_comp_fromZero (f : 𝒜 →+*ᵍ ℬ) (s : A) :
    (Away.map f s).comp (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (f s))).comp (degreeZeroMap f) := by
  ext a
  dsimp only [RingHom.comp_apply, Away.map, fromZeroRingHom]
  simp [HomogeneousLocalization.map_mk, degreeZeroMap]

set_option backward.isDefEq.respectTransparency false in
/-- The induced Proj morphism commutes with the maps to degree-zero spectra. -/
theorem map_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (degreeZeroMap f)) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2,
    Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (awayMap_comp_fromZero f s.2)

/-- Scalar compatibility on actual degree-zero rings gives compatibility over
the spectrum of any common coefficient ring. -/
theorem map_toSpec_base (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {R : Type u} [CommRing R] (α : R →+* 𝒜 0) (β : R →+* ℬ 0)
    (hcompat : (degreeZeroMap f).comp α = β) :
    Proj.map f hf ≫ (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom α)) =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom β) := by
  rw [← Category.assoc, map_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom hcompat

end DeJongAlterations.Geometry.ProjStructureMap
