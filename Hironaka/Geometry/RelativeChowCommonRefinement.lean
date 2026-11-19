import Hironaka.Geometry.RelativeChow

/-!
# Genuine projective common refinements over affine Noetherian domains

The actual reduced fibre-product component construction gives the common
alteration. Its Noetherianity is derived from its actual proper structure.
The genuine arbitrary-ring Chow construction then gives an actual projective
refinement. Every comparison and every exact triangle is retained.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Source 5.4 for any actual finite family over an affine integral
Noetherian base, including the empty family. The projective presentation
is constructed by genuine Chow, not supplied by the caller. -/
theorem exists_projective_finite_common_refinement [IsDomain R] (n : ℕ)
    (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, IsAlteration (f i)) :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of R)) (a : ∀ i, W ⟶ Y i),
      IsAlteration q ∧ IsProjectiveOver q ∧
      (∀ i, IsAlteration (a i)) ∧ (∀ i, a i ≫ f i = q) := by
  obtain ⟨V, r, b, hr, hb, htri⟩ :=
    AlterationCommonRefinement.exists_finite_common_refinement n Y f hf
  let := hr
  let := hr.sourceIntegral
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian r
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace r
  let : AlgebraicGeometry.IsNoetherian V := ⟨⟩
  obtain ⟨W, π, hπ, hproj⟩ := exists_projective_modification_of_isProper r
  let := hπ
  refine ⟨W, π ≫ r, fun i => π ≫ b i, IsAlteration.comp π r, hproj, ?_, ?_⟩
  · intro i
    let := hb i
    exact IsAlteration.comp π (b i)
  · intro i
    rw [Category.assoc, htri]

/-- The two-alteration form over any affine Noetherian coefficient ring;
integrality of the base is obtained from the actual input alterations. -/
theorem exists_projective_common_refinement
    {Y₁ Y₂ : Scheme.{u}}
    (f : Y₁ ⟶ Spec (CommRingCat.of R)) (g : Y₂ ⟶ Spec (CommRingCat.of R))
    [hf : IsAlteration f] [hg : IsAlteration g] :
    ∃ (W : Scheme.{u}) (a : W ⟶ Y₁) (b : W ⟶ Y₂),
      IsAlteration a ∧ IsAlteration b ∧ IsAlteration (a ≫ f) ∧
      IsProjectiveOver (a ≫ f) ∧ a ≫ f = b ≫ g := by
  obtain ⟨V, r, s, hr, hs, hrs⟩ := AlterationCommonRefinement.exists_common_refinement f g
  let := hr
  let := hs
  let := hr.sourceIntegral
  let : IsAlteration (r ≫ f) := IsAlteration.comp r f
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (r ≫ f)
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (r ≫ f)
  let : AlgebraicGeometry.IsNoetherian V := ⟨⟩
  obtain ⟨W, π, hπ, hproj⟩ := exists_projective_modification_of_isProper (r ≫ f)
  let := hπ
  let : IsAlteration (π ≫ r) := IsAlteration.comp π r
  refine ⟨W, π ≫ r, π ≫ s, inferInstance, IsAlteration.comp π s,
    IsAlteration.comp (π ≫ r) f, ?_, ?_⟩
  · simpa only [Category.assoc] using hproj
  · rw [Category.assoc, hrs, Category.assoc]

end Hironaka.Geometry.RelativeChow
