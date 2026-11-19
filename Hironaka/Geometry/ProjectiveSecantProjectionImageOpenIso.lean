import Hironaka.Geometry.ProjectiveSecantProjectionBirational
import Hironaka.Geometry.ProjectiveSecantProjectionImageFactorIso

/-!
# Genuine actual finite-image isomorphism neighbourhoods without global reducedness or integrality
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual schematic dominance internally supplies the SAME original finite chart injection, retaining genuine native finite Nakayama bijectivity without source/target reducedness. -/
theorem exists_schematicallyDominant_finite_chart_awayMap_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsSchemeTheoreticallyDominant f]
    (x : X) (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U)
    (hfibre : ∀ z : X, f z = f x → z = x)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) [IsIso (f.residueFieldMap x)] :
    ∃ Q : PrimeSpectrum Γ(X, f ⁻¹ᵁ U), (hU.preimage f).fromSpec Q = x ∧
      ∃ r ∉ (PrimeSpectrum.comap (f.app U).hom Q).asIdeal,
        ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (f.app U).hom r') := by
  let hV := hU.preimage f
  have hr : x ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hx
  obtain ⟨Q, rfl⟩ := hr
  have ht : hV.fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm
  have hβinj : Function.Injective (f.app U).hom := f.app_injective U
  have hβfibre := chart_fibre_eq_of_original f hV.fromSpec hU.fromSpec (f.app U) ht Q hfibre
  have hβfu := chart_stalkMap_formallyUnramified_of_original f hV.fromSpec hU.fromSpec (f.app U) ht Q hfu
  let : IsIso ((Spec.map (f.app U)).residueFieldMap Q) :=
    chart_residueFieldMap_isIso_of_original f hV.fromSpec hU.fromSpec (f.app U) ht Q
  exact ⟨Q, rfl, exists_awayMap_bijective_of_spec_local_data (f.app U) (f.finite_app U hU)
    hβinj Q hβfibre hβfu⟩

/-- The SAME actual finite schematically dominant map internally has an actual original target isomorphism neighbourhood from the original point local data, without reducedness/integrality. -/
theorem exists_schematicallyDominant_finite_target_open_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsSchemeTheoreticallyDominant f]
    (x : X) (hfibre : ∀ z : X, f z = f x → z = x)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) [IsIso (f.residueFieldMap x)] :
    ∃ W : Y.Opens, f x ∈ W ∧ IsIso (f ∣_ W) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨Q, hQ, r, hr, hbij⟩ := exists_schematicallyDominant_finite_chart_awayMap_bijective f x U hU hxU hfibre hfu
  let b := Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec
  refine ⟨b.opensRange, ?_, isIso_original_morphismRestrict_of_awayMap_bijective f U hU r (hbij r dvd_rfl)⟩
  have hP : Spec.map (f.app U) Q ∈
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r)))).opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hr
  change f x ∈ (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec).opensRange
  rw [Scheme.Hom.opensRange_comp]
  refine ⟨Spec.map (f.app U) Q, hP, ?_⟩
  have ht : Spec.map (f.app U) ≫ hU.fromSpec = (hU.preimage f).fromSpec ≫ f := by
    simpa only [← Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl)
  have hh := congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => m Q) ht
  change hU.fromSpec (Spec.map (f.app U) Q) = f ((hU.preimage f).fromSpec Q) at hh
  exact hh.trans (congrArg (fun z => f z) hQ)

/-- The SAME actual finite map internally produces an actual isomorphism neighbourhood in its SAME native scheme image from original point local data, with NO reducedness, integrality, dominance or image certificate. -/
theorem exists_native_image_target_open_isIso_of_finite_point_data
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hfibre : ∀ z : X, f z = f x → z = x)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) [IsIso (f.residueFieldMap x)] :
    ∃ W : f.image.Opens, f.toImage x ∈ W ∧ IsIso (f.toImage ∣_ W) := by
  let : IsFinite f.toImage := toImage_isFinite f
  let : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
  let : IsIso (f.imageι.residueFieldMap (f.toImage x)) :=
    residueFieldMap_isIso_of_comp (𝟙 f.image) f.imageι (f.toImage x)
  let : IsIso (f.toImage.residueFieldMap x) := by
    have hc : IsIso ((f.toImage ≫ f.imageι).residueFieldMap x) := by
      rw [f.toImage_imageι]
      infer_instance
    rw [Scheme.residueFieldMap_comp] at hc
    let := hc
    exact IsIso.of_isIso_comp_left (f.imageι.residueFieldMap (f.toImage x)) _
  apply exists_schematicallyDominant_finite_target_open_isIso f.toImage x
  · intro z hz
    apply hfibre
    have h := congrArg (fun q => f.imageι q) hz
    change (f.toImage ≫ f.imageι) z = (f.toImage ≫ f.imageι) x at h
    rwa [f.toImage_imageι] at h
  · exact toImage_stalkMap_formallyUnramified f x hfu

end Hironaka.Geometry.ProjectiveSecant
