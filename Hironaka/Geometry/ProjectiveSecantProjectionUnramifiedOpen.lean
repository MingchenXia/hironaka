import Hironaka.Geometry.ProjectiveSecantProjectionLocalBridge
import Mathlib.RingTheory.Unramified.Locus

/-!
# Actual source opens for the same original formally unramified projection stalk
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal entire original chart map internally chooses a source localization, whose actual original open image contains the SAME original point and makes the SAME original morphism formally unramified. -/
theorem exists_formallyUnramified_open_of_chart
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {R S : CommRingCat.{u}}
    (a : Spec S ⟶ X) [IsOpenImmersion a] (b : Spec R ⟶ Y) [IsOpenImmersion b]
    (β : R ⟶ S) (ht : a ≫ f = Spec.map β ≫ b) (Q : PrimeSpectrum S)
    (hAt : letI := β.hom.toAlgebra; Algebra.IsUnramifiedAt R Q.asIdeal) :
    ∃ V : X.Opens, a Q ∈ V ∧ FormallyUnramified (V.ι ≫ f) := by
  let : Algebra R S := β.hom.toAlgebra
  let : Algebra.IsUnramifiedAt R Q.asIdeal := hAt
  let : LocallyOfFiniteType (Spec.map β ≫ b) := by rw [← ht]; infer_instance
  have hft : β.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    (locallyOfFiniteType_of_comp (Spec.map β) b)
  let : Algebra.FiniteType R S := hft
  obtain ⟨r, hr, hfu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) Q.asIdeal
  let : Algebra.FormallyUnramified R (Localization.Away r) := hfu
  let l : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))
  let c := l ≫ a
  let γ : R ⟶ CommRingCat.of (Localization.Away r) :=
    CommRingCat.ofHom ((algebraMap S (Localization.Away r)).comp β.hom)
  have hc : c ≫ f = Spec.map γ ≫ b := by
    dsimp only [c, l, γ]
    rw [Category.assoc, ht, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hγ : γ.hom = algebraMap R (Localization.Away r) :=
    (IsScalarTower.algebraMap_eq R S (Localization.Away r)).symm
  have hγfu : γ.hom.FormallyUnramified := by
    rw [hγ, RingHom.formallyUnramified_algebraMap]
    exact hfu
  let : FormallyUnramified (Spec.map γ) :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr hγfu
  let : FormallyUnramified (c ≫ f) := by
    rw [hc]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  have hQ : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨Q', hQ'⟩ := hQ
  refine ⟨c.opensRange, ?_, ?_⟩
  · change a Q ∈ Set.range c
    refine ⟨Q', ?_⟩
    change a (PrimeSpectrum.comap (algebraMap S (Localization.Away r)) Q') = a Q
    exact congrArg (fun z => a z) hQ'
  · rw [← c.isoOpensRange_inv_comp, Category.assoc]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance

/-- Original stalk unramifiedness internally chooses both entire original affine charts and an actual source open containing that SAME original point; no local-open certificate is supplied. -/
theorem exists_formallyUnramified_open_of_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ V : X.Opens, x ∈ V ∧ FormallyUnramified (V.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).isOpen
  obtain ⟨Q, hQ⟩ : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
  have ht : hV.fromSpec ≫ f = Spec.map (f.appLE U V hVU) ≫ hU.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  have hAt := isUnramifiedAt_of_spec_stalkMap (f.appLE U V hVU) Q
    (chart_stalkMap_formallyUnramified_of_original f hV.fromSpec hU.fromSpec
      (f.appLE U V hVU) ht Q (hQ ▸ hfu))
  obtain ⟨W, hxW, hW⟩ := exists_formallyUnramified_open_of_chart f hV.fromSpec hU.fromSpec
    (f.appLE U V hVU) ht Q hAt
  exact ⟨W, hQ ▸ hxW, hW⟩

end Hironaka.Geometry.ProjectiveSecant
