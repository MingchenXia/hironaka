import DeJongAlterations.Geometry.BlowupGluing
import DeJongAlterations.Geometry.SpecIdealSheaf

/-!
# Actual affine restrictions of the global ideal-sheaf blowup

The canonical affine Rees charts are the genuine inverse-image open
subschemes. Over an affine spectrum the global construction is identified
with the original ring's Rees blowup, with its original structure morphism.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.BlowupAffineComparison

open BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The actual native affine chart is the inverse-image open subscheme. -/
def chartRestrictionIso (U : X.AffineZariskiSite) :
    affineBlowup (D.ideal ⟨U.1, U.2⟩) ≅ (blowupStructure D ⁻¹ᵁ U.1).toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartInclusion D U)
    (blowupStructure D ⁻¹ᵁ U.1).ι (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (chartInclusion_opensRange D U))

@[reassoc (attr := simp)]
theorem chartRestrictionIso_hom_ι (U : X.AffineZariskiSite) :
    (chartRestrictionIso D U).hom ≫ (blowupStructure D ⁻¹ᵁ U.1).ι =
      chartInclusion D U := by
  simp [chartRestrictionIso]

/-- The restriction isomorphism retains the actual original affine base map. -/
@[reassoc]
theorem chartRestrictionIso_hom_structure (U : X.AffineZariskiSite) :
    (chartRestrictionIso D U).hom ≫ (blowupStructure D ∣_ U.1) ≫ U.1.ι =
      affineBlowupStructure (D.ideal ⟨U.1, U.2⟩) ≫ U.2.fromSpec := by
  rw [morphismRestrict_ι, ← Category.assoc, chartRestrictionIso_hom_ι,
    chartInclusion_structure]

instance topChartInclusion_isIso [IsAffine X] :
    IsIso (chartInclusion D ⟨⊤, isAffineOpen_top X⟩) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [chartInclusion_opensRange]
  simp

/-- The entire global blowup on an affine scheme is its actual top affine Rees chart. -/
def affineTopIso [IsAffine X] :
    affineBlowup (D.ideal ⟨⊤, isAffineOpen_top X⟩) ≅ blowup D :=
  asIso (chartInclusion D ⟨⊤, isAffineOpen_top X⟩)

@[reassoc]
theorem affineTopIso_hom_structure [IsAffine X] :
    (affineTopIso D).hom ≫ blowupStructure D =
      affineBlowupStructure (D.ideal ⟨⊤, isAffineOpen_top X⟩) ≫
        (isAffineOpen_top X).fromSpec :=
  chartInclusion_structure D ⟨⊤, isAffineOpen_top X⟩

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The genuine global blowup on a spectrum is the original ring's native affine blowup. -/
def specBlowupIso : affineBlowup I ≅ blowup (SpecIdealSheaf.specIdealSheaf R I) :=
  (affineBlowupRingEquiv I
    ((SpecIdealSheaf.specIdealSheaf R I).ideal ⟨⊤, isAffineOpen_top _⟩)
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
    (SpecIdealSheaf.specIdealSheaf_ideal_top R I).symm).symm.trans
      (affineTopIso (SpecIdealSheaf.specIdealSheaf R I))

/-- The spectrum comparison is over the original coefficient spectrum. -/
@[reassoc]
theorem specBlowupIso_hom_structure :
    (specBlowupIso R I).hom ≫ blowupStructure (SpecIdealSheaf.specIdealSheaf R I) =
      affineBlowupStructure I := by
  let J := (SpecIdealSheaf.specIdealSheaf R I).ideal ⟨⊤, isAffineOpen_top _⟩
  let e := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have hIJ : I.map e.toRingHom = J := (SpecIdealSheaf.specIdealSheaf_ideal_top R I).symm
  let E := affineBlowupRingEquiv I J e hIJ
  have hE : E.hom ≫ affineBlowupStructure I =
      affineBlowupStructure J ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
    affineBlowupMapTo_structure I J e.toRingHom hIJ
  change (E.inv ≫ (affineTopIso (SpecIdealSheaf.specIdealSheaf R I)).hom) ≫ _ = _
  rw [Category.assoc, affineTopIso_hom_structure, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv]
  change E.inv ≫ affineBlowupStructure J ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = _
  rw [← hE, Iso.inv_hom_id_assoc]

end DeJongAlterations.Geometry.BlowupAffineComparison
