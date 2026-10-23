import DeJongAlterations.Geometry.BlowupAffineComparison

/-!
# Native global blowup charts from arbitrary spectrum open immersions

The actual coordinate ring equivalence is constructed from native open
immersion section maps. It transports the full pulled-back ideal and produces
the actual Rees blowup chart, with its Cartesian original-base square.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.BlowupOpenChart

open BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion f]

/-- The actual affine open image of the whole given spectrum chart. -/
abbrev baseOpen : X.affineOpens :=
  ⟨f ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion f⟩

/-- The actual native coefficient isomorphism, with no chosen chart identifications. -/
def coefficients : R ≃+* Γ(X, (baseOpen f).1) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).symm ≪≫ (f.appIso ⊤).symm).commRingCatIsoToRingEquiv

/-- The full pulled-back ideal determines the actual ideal on the chart image. -/
theorem ideal_map_coefficients (D : X.IdealSheafData) (I : Ideal R)
    (hDI : D.comap f = SpecIdealSheaf.specIdealSheaf R I) :
    I.map (coefficients f).toRingHom = D.ideal (baseOpen f) := by
  have hs := congrArg (fun E : (Spec (CommRingCat.of R)).IdealSheafData =>
    E.ideal ⟨⊤, isAffineOpen_top _⟩) hDI
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    SpecIdealSheaf.specIdealSheaf_ideal_top] at hs
  change I.map ((f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) = _
  rw [← Ideal.map_map, ← hs]
  exact Ideal.map_comap_of_surjective (f.appIso ⊤).inv.hom
    (ConcreteCategory.bijective_of_isIso (f.appIso ⊤).inv).surjective _

/-- The actual image-chart map is the original open immersion after coefficient change. -/
theorem fromSpec_eq :
    (baseOpen f).2.fromSpec = Spec.map (CommRingCat.ofHom (coefficients f).toRingHom) ≫ f := by
  apply (cancel_epi (Spec.map (f.appIso ⊤).hom)).mp
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (baseOpen f).2 (isAffineOpen_top _)
    (f.preimage_image_eq ⊤).ge
  rw [← Scheme.Hom.appIso_hom', IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change Spec.map (f.appIso ⊤).hom ≫ (baseOpen f).2.fromSpec =
    Spec.map (f.appIso ⊤).hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (f.appIso ⊤).inv) ≫ f
  simpa only [← Spec.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

variable (D : X.IdealSheafData) (I : Ideal R)
    (hDI : D.comap f = SpecIdealSheaf.specIdealSheaf R I)

/-- The actual affine Rees chart map into the global blowup. -/
def chartMap : affineBlowup I ⟶ blowup D :=
  (affineBlowupRingEquiv I (D.ideal (baseOpen f)) (coefficients f)
    (ideal_map_coefficients f D I hDI)).inv ≫ chartInclusion D (baseOpen f)

/-- Its original base triangle is exact. -/
@[reassoc]
theorem chartMap_structure :
    chartMap f D I hDI ≫ blowupStructure D = affineBlowupStructure I ≫ f := by
  let E := affineBlowupRingEquiv I (D.ideal (baseOpen f)) (coefficients f)
    (ideal_map_coefficients f D I hDI)
  have hE : E.hom ≫ affineBlowupStructure I =
      affineBlowupStructure (D.ideal (baseOpen f)) ≫
        Spec.map (CommRingCat.ofHom (coefficients f).toRingHom) :=
    affineBlowupMapTo_structure I _ _ _
  change (E.inv ≫ chartInclusion D (baseOpen f)) ≫ _ = _
  rw [Category.assoc, chartInclusion_structure, fromSpec_eq,
    ← Category.assoc (affineBlowupStructure _), ← hE]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

instance chartMap_isOpenImmersion : IsOpenImmersion (chartMap f D I hDI) := by
  unfold chartMap
  infer_instance

/-- The exact native chart image is the entire inverse image of the original open chart. -/
theorem chartMap_opensRange :
    (chartMap f D I hDI).opensRange = blowupStructure D ⁻¹ᵁ f.opensRange := by
  dsimp only [chartMap]
  rw [Scheme.Hom.opensRange_comp_of_isIso, chartInclusion_opensRange]
  congr 1
  exact f.image_top_eq_opensRange

/-- The actual original-base square, derived from the full image formula. -/
theorem chart_isPullback :
    IsPullback (affineBlowupStructure I) (chartMap f D I hDI) f (blowupStructure D) := by
  apply IsOpenImmersion.isPullback
  · exact chartMap_structure f D I hDI
  · exact (chartMap_opensRange f D I hDI).symm

/-- The actual inverse-image open subscheme is the original ring's affine Rees blowup. -/
def chartIso : affineBlowup I ≅ (blowupStructure D ⁻¹ᵁ f.opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartMap f D I hDI)
    (blowupStructure D ⁻¹ᵁ f.opensRange).ι (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (chartMap_opensRange f D I hDI))

@[reassoc (attr := simp)]
theorem chartIso_hom_ι :
    (chartIso f D I hDI).hom ≫ (blowupStructure D ⁻¹ᵁ f.opensRange).ι =
      chartMap f D I hDI := by
  simp [chartIso]

end DeJongAlterations.Geometry.BlowupOpenChart
