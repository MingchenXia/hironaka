import Hironaka.Resolution.Algebraic.ActualHistoryOriginalRegularIsomorphism
import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Hironaka.Scheme.BlowUpSequence.Projective

/-!
# ONE actual strong resolution of the ORIGINAL mixed-dimensional affine input

Source-first proof: `actual-mixed-dimension-affine-resolution-20261102.tex`.
The original separation step and SAME descended A/BP histories are genuine
native blowups with their original clocks and true ORIGINAL singular support.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualMixedDimensionAffineResolution

noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupRegularLocus ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualDescendedHistorySmoothEndpoint ActualOriginalSingPrincipalizationHistoryDescent
  ActualPrincipalizedEndpointGeometry ActualPrincipalizationCanonicalBoundary ActualSplitSncReflection
  ActualHistoryOriginalRegularIsomorphism

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

private abbrev originalStructure : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

private instance originalStructure_finiteType : FiniteType (originalStructure R k) := by
  have : LocallyOfFiniteType (originalStructure R k) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance

private instance originalStructure_separated : IsSeparated (originalStructure R k) := inferInstance

/-- The actual ORIGINAL dimension-separation centre as a native ideal sheaf. -/
def separationCentre : (Spec (.of R)).IdealSheafData := specIdealSheaf (dimensionSeparationIdeal R)

omit [IsReduced R] in
private theorem exists_separationIso :
    ∃ e : (separationCentre R).blowUp ≅ affineBlowUp (dimensionSeparationIdeal R),
      e.hom ≫ affineBlowUp.π (dimensionSeparationIdeal R) = (separationCentre R).blowUpπ := by
  obtain ⟨e,he,-⟩ := IsBlowUp.exists_iso (blowUp.isBlowUp (separationCentre R))
    (affineBlowUp.isBlowUp (dimensionSeparationIdeal R))
  exact ⟨e,he⟩

/-- Genuine isomorphism of the two actual blowups of the SAME original separation centre. -/
def separationIso : (separationCentre R).blowUp ≅ affineBlowUp (dimensionSeparationIdeal R) :=
  Classical.choose (exists_separationIso R)

omit [IsReduced R] in
/-- Its actual projection equation is over the ORIGINAL scheme. -/
theorem separationIso_over : (separationIso R).hom ≫ affineBlowUp.π (dimensionSeparationIdeal R) =
    (separationCentre R).blowUpπ := Classical.choose_spec (exists_separationIso R)

private def descendedHistory : (affineBlowUp (dimensionSeparationIdeal R)).BlowUpSequence :=
  (nativeBaseHistory R k).concat (nativeBasePrincipalizationHistory R k)

private def transportedTail : (separationCentre R).blowUp.BlowUpSequence :=
  (descendedHistory R k).pullback (separationIso R).hom

/-- ONE actual original history: genuine separation step followed by the SAME two descended histories. -/
def originalHistory : (Spec (.of R)).BlowUpSequence :=
  .cons (Spec (.of R)) (separationCentre R) (transportedTail R k)

/-- The exact original clock retains every internal position of both SAME descended histories. -/
theorem originalHistory_length : (originalHistory R k).length =
    (nativeBaseHistory R k).length + (nativeBasePrincipalizationHistory R k).length + 1 := by
  change ((descendedHistory R k).pullback (separationIso R).hom).length + 1 = _
  rw [length_pullback]
  exact congrArg (· + 1) (length_concat _ _)

private instance transportedTailLast_isIso :
    IsIso ((descendedHistory R k).pullbackLastHom (separationIso R).hom) :=
  property_of_isPullback (MorphismProperty.isomorphisms Scheme)
    (ActualFinalClopenProductPresentation.lastStage_isPullback (descendedHistory R k) (separationIso R).hom)
    inferInstance

/-- Actual endpoint isomorphism to the SAME genuine descended ORIGINAL-singular BP endpoint. -/
def originalEndpointIso : (originalHistory R k).last ≅ (nativeBasePrincipalizationHistory R k).last :=
  asIso ((descendedHistory R k).pullbackLastHom (separationIso R).hom) ≪≫
    eqToIso (last_concat (nativeBaseHistory R k) (nativeBasePrincipalizationHistory R k))

/-- The actual assembled composite is EXACTLY the proved original three-phase projection. -/
theorem originalHistory_composite : (originalHistory R k).composite =
    (originalEndpointIso R k).hom ≫ (nativeBasePrincipalizationHistory R k).composite ≫
      (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by
  change ((descendedHistory R k).pullback (separationIso R).hom).composite ≫
    (separationCentre R).blowUpπ =
      ((descendedHistory R k).pullbackLastHom (separationIso R).hom ≫
        eqToHom (last_concat (nativeBaseHistory R k) (nativeBasePrincipalizationHistory R k))) ≫
          (nativeBasePrincipalizationHistory R k).composite ≫ (nativeBaseHistory R k).composite ≫
            affineBlowUp.π (dimensionSeparationIdeal R)
  calc
    _ = (descendedHistory R k).pullbackLastHom (separationIso R).hom ≫
        (descendedHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by
      rw [← Category.assoc,pullbackLastHom_comp_composite,Category.assoc,separationIso_over]
    _ = (descendedHistory R k).pullbackLastHom (separationIso R).hom ≫
        (eqToHom (last_concat (nativeBaseHistory R k) (nativeBasePrincipalizationHistory R k)) ≫
          (nativeBasePrincipalizationHistory R k).composite ≫ (nativeBaseHistory R k).composite) ≫
            affineBlowUp.π (dimensionSeparationIdeal R) :=
      congrArg (fun f => (descendedHistory R k).pullbackLastHom (separationIso R).hom ≫ f ≫
        affineBlowUp.π (dimensionSeparationIdeal R)) (composite_concat _ _)
    _ = _ := by simp only [Category.assoc]

/-- Projectivity is proved for the genuine assembled history itself. -/
theorem originalHistory_isProjective : IsProjective (originalHistory R k).composite := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsNoetherian (Spec (.of R)) := inferInstance
  exact (originalHistory R k).isProjective_composite

/-- Properness is proved for the genuine assembled history itself. -/
theorem originalHistory_isProper : IsProper (originalHistory R k).composite := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsNoetherian (Spec (.of R)) := inferInstance
  exact (originalHistory R k).isProper_composite

private abbrev finalBaseStructure : (nativeBasePrincipalizationHistory R k).last ⟶ Spec (.of k) :=
  (nativeBasePrincipalizationHistory R k).composite ≫
    (nativeBaseHistory R k).composite ≫ separationStructure R k

private instance finalBaseStructure_smooth : Smooth (finalBaseStructure R k) :=
  nativePrincipalizedBase_smooth R k

/-- Genuine smoothness of the assembled actual endpoint over the ORIGINAL coefficient field. -/
theorem originalHistory_smooth : Smooth ((originalHistory R k).composite ≫ originalStructure R k) := by
  have he : (originalHistory R k).composite ≫ originalStructure R k =
      (originalEndpointIso R k).hom ≫ finalBaseStructure R k := by
    rw [originalHistory_composite]
    rfl
  rw [he]
  infer_instance

/-- The ENTIRE ORIGINAL regular open is preserved by the SAME actual assembled history. -/
theorem originalHistory_isIso_over_regular :
    IsIso ((originalHistory R k).composite ∣_ (originalStructure R k).smoothLocus) := by
  let U := (originalStructure R k).smoothLocus
  have : IsIso (affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U) :=
    separation_isIso_over_smoothLocus R k
  have : IsIso ((nativeBaseHistory R k).composite ∣_
      (affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ U) :=
    nativeBaseHistory_isIso_over_original_regular R k
  have : IsIso (((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ∣_ U) :=
    isIso_restrict_comp _ _ U
  have : IsIso ((nativeBasePrincipalizationHistory R k).composite ∣_
      ((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ U) :=
    nativeBasePrincipalizationHistory_isIso_over_original_regular R k
  have : IsIso (((nativeBasePrincipalizationHistory R k).composite ≫
      (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ∣_ U) :=
    isIso_restrict_comp _ _ U
  have : IsIso (((originalEndpointIso R k).hom ≫ (nativeBasePrincipalizationHistory R k).composite ≫
      (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ∣_ U) :=
    isIso_restrict_comp _ _ U
  exact isIso_restrict_congr (originalHistory_composite R k).symm U

/-- The ORIGINAL finite-type separated affine input, with no equidimensionality hypothesis. -/
def originalAlgScheme : AlgScheme k := .ofHom (originalStructure R k) inferInstance inferInstance

/-- True SNC of the inverse ORIGINAL singular support under the ONE actual assembled history. -/
theorem originalHistory_originalSing_isSnc : Scheme.IsSncDivisor
    ((originalHistory R k).composite ⁻¹' ((originalStructure R k).smoothLocus : Set (Spec (.of R)))ᶜ) := by
  refine ⟨(nativeBaseBoundary R k).comap (originalEndpointIso R k).hom,?_,?_⟩
  · exact isSnc_comap_of_smooth (finalBaseStructure R k) (originalEndpointIso R k).hom
      (nativeBaseBoundary_isSnc R k)
  · rw [Hironaka.Resolution.coe_support_comap,nativeBaseBoundary_original_support,
      nativePrincipalizedOriginalIdeal,support_comap,Closeds.coe_preimage,
      Scheme.coe_support_singIdeal_eq_singularLocus (originalStructure R k),
      Scheme.singularLocus_eq_compl_smoothLocus (originalStructure R k),originalHistory_composite]
    rfl

/-- Genuine native strong resolution of every reduced mixed-dimensional finite-type affine input. -/
theorem originalHistory_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (originalAlgScheme R k) (originalHistory R k) := by
  have hreg : IsIso ((originalHistory R k).composite ∣_ (originalStructure R k).smoothLocus) :=
    originalHistory_isIso_over_regular R k
  refine ⟨⟨originalHistory_smooth R k,originalHistory_isProjective R k,
    (originalStructure R k).smoothLocus,(originalStructure R k).dense_smoothLocus_of_perfectField,hreg⟩,
    hreg,originalHistory_originalSing_isSnc R k⟩
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualMixedDimensionAffineResolution
