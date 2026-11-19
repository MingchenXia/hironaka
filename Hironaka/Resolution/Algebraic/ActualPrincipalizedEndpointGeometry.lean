import Hironaka.Resolution.Algebraic.ActualOriginalSingPrincipalizationHistoryDescent
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Centers

/-!
# Actual terminal geometry of the SAME descended original-singular principalization

Source-first proof: `actual-principalized-endpoint-geometry-20261102.tex`.
The genuine terminal original ideal and its actual affine split SNC pullback
are constructed; the downstairs SNC reflection remains a separate theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualPrincipalizedEndpointGeometry

noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualDescendedHistorySmoothEndpoint ActualPaddedNativePrincipalizationInput
  ActualOriginalSingPrincipalizationHistoryDescent ActualFinalClopenProductPresentation

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

private abbrev baseStructure : (nativeBaseHistory R k).last ⟶ Spec (.of k) :=
  (nativeBaseHistory R k).composite ≫ separationStructure R k

private instance baseStructure_smooth : Smooth (baseStructure R k) := nativeBaseHistory_smooth R k

private instance baseLocallyNoetherian : IsLocallyNoetherian (nativeBaseHistory R k).last :=
  LocallyOfFiniteType.isLocallyNoetherian (baseStructure R k)

private instance basePrincipalization_proper : IsProper (nativeBasePrincipalizationHistory R k).composite :=
  (nativeBasePrincipalizationHistory R k).isProper_composite

private abbrev paddedStructure : (nativePaddedHistory R k).last ⟶ Spec (.of k) :=
  (nativeOriginalSingPrincipalizationTriple R k).X.hom

private theorem paddedPrincipalization_smooth :
    Smooth ((nativeOriginalSingPrincipalizationHistory R k).composite ≫ paddedStructure R k) := by
  let T := nativeOriginalSingPrincipalizationTriple R k
  obtain ⟨n,hn⟩ := T.smoothOfRelativeDimension
  have : SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k)) := hn
  change Smooth ((BP T).composite ≫ (T.X.left ↘ Spec (.of k)))
  exact IsSmooth.smooth_stageMap (n := n) (BP_isOrderGeSeq_zero T).1 (Fin.last _)

/-- The actual previous terminal projection is affine by its genuine native pullback geometry. -/
theorem paddedFinalProjection_affine : IsAffineHom (paddedFinalProjection R k) := by
  have : Smooth (envelopeProjection R k) := envelopeProjection_smooth R k
  have : IsAffineHom (envelopeProjection R k) := envelopeProjection_isAffineHom R k
  have : IsAffineHom ((nativeBaseHistory R k).pullbackLastHom (envelopeProjection R k)) :=
    property_of_isPullback _ (lastStage_isPullback (nativeBaseHistory R k) (envelopeProjection R k))
      (inferInstance : IsAffineHom (envelopeProjection R k))
  dsimp only [paddedFinalProjection]
  infer_instance

private def principalizationLastIso : (nativeOriginalSingPrincipalizationHistory R k).last ≅
    ((nativeBasePrincipalizationHistory R k).pullback (paddedFinalProjection R k)).last :=
  eqToIso (congrArg Scheme.BlowUpSequence.last (nativePrincipalization_canonical_history_descends R k))

/-- The actual final projection of the SAME native principalization onto its SAME descended endpoint. -/
def nativePrincipalizedProjection : (nativeOriginalSingPrincipalizationHistory R k).last ⟶
    (nativeBasePrincipalizationHistory R k).last :=
  (principalizationLastIso R k).hom ≫
    (nativeBasePrincipalizationHistory R k).pullbackLastHom (paddedFinalProjection R k)

/-- The actual principalized final map has the genuine native last-stage projection equation. -/
theorem nativePrincipalizedProjection_over :
    nativePrincipalizedProjection R k ≫ (nativeBasePrincipalizationHistory R k).composite =
      (nativeOriginalSingPrincipalizationHistory R k).composite ≫ paddedFinalProjection R k := by
  rw [nativePrincipalizedProjection,Category.assoc,pullbackLastHom_comp_composite,← Category.assoc]
  exact congrArg (fun h => h ≫ paddedFinalProjection R k)
    (eqToHom_comp_composite_of_eq (nativePrincipalization_canonical_history_descends R k))

/-- Smoothness is derived by actual last-stage base change and the SAME native equality transport. -/
theorem nativePrincipalizedProjection_smooth : Smooth (nativePrincipalizedProjection R k) := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  have : Smooth ((nativeBasePrincipalizationHistory R k).pullbackLastHom (paddedFinalProjection R k)) :=
    smooth_pullbackLastHom _ _
  dsimp only [nativePrincipalizedProjection]
  infer_instance

/-- Affineness is derived by the actual final cartesian square. -/
theorem nativePrincipalizedProjection_affine : IsAffineHom (nativePrincipalizedProjection R k) := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  have : IsAffineHom (paddedFinalProjection R k) := paddedFinalProjection_affine R k
  have : IsAffineHom ((nativeBasePrincipalizationHistory R k).pullbackLastHom (paddedFinalProjection R k)) :=
    property_of_isPullback _ (lastStage_isPullback (nativeBasePrincipalizationHistory R k)
      (paddedFinalProjection R k)) (inferInstance : IsAffineHom (paddedFinalProjection R k))
  dsimp only [nativePrincipalizedProjection]
  infer_instance

private def principalizationPullbackSection : (nativeBasePrincipalizationHistory R k).last ⟶
    ((nativeBasePrincipalizationHistory R k).pullback (paddedFinalProjection R k)).last := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  exact (lastStage_isPullback (nativeBasePrincipalizationHistory R k) (paddedFinalProjection R k)).lift
    (𝟙 _) ((nativeBasePrincipalizationHistory R k).composite ≫ nativeFinalSection R k)
      (by simp [Category.assoc,nativeFinalSection_projection])

/-- Actual section, internally constructed by the genuine terminal cartesian lift. -/
def nativePrincipalizedSection : (nativeBasePrincipalizationHistory R k).last ⟶
    (nativeOriginalSingPrincipalizationHistory R k).last :=
  principalizationPullbackSection R k ≫ (principalizationLastIso R k).inv

/-- The internally constructed actual section retracts the SAME actual terminal projection. -/
theorem nativePrincipalizedSection_projection :
    nativePrincipalizedSection R k ≫ nativePrincipalizedProjection R k =
      𝟙 (nativeBasePrincipalizationHistory R k).last := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  rw [nativePrincipalizedSection,nativePrincipalizedProjection,Category.assoc,Iso.inv_hom_id_assoc]
  exact (lastStage_isPullback (nativeBasePrincipalizationHistory R k) (paddedFinalProjection R k)).lift_fst _ _ _

private theorem paddedFinalProjection_structure :
    paddedFinalProjection R k ≫ baseStructure R k = paddedStructure R k := by
  change paddedFinalProjection R k ≫ ((nativeBaseHistory R k).composite ≫
    affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      (nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
        affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  rw [← Category.assoc,paddedFinalProjection_over,Category.assoc]

/-- The final scheme of the SAME genuine descended principalization is smooth over the original field. -/
theorem nativePrincipalizedBase_smooth :
    Smooth ((nativeBasePrincipalizationHistory R k).composite ≫ baseStructure R k) := by
  let C := nativeBasePrincipalizationHistory R k
  let q := paddedFinalProjection R k
  have : Smooth q := paddedFinalProjection_smooth R k
  have : IsAffineHom q := paddedFinalProjection_affine R k
  have : Smooth ((C.pullback q).composite ≫ q ≫ baseStructure R k) := by
    rw [← nativePrincipalization_canonical_history_descends,paddedFinalProjection_structure]
    exact paddedPrincipalization_smooth R k
  have : Smooth ((C.pullback q).stageMap (C.pullbackStageIdx q (Fin.last _)) ≫ q ≫ baseStructure R k) := by
    rw [pullbackStageIdx_last]
    change Smooth ((C.pullback q).composite ≫ q ≫ baseStructure R k)
    infer_instance
  have : LocallyOfFinitePresentation (C.stageMap (Fin.last _) ≫ baseStructure R k) := by
    change LocallyOfFinitePresentation (C.composite ≫ baseStructure R k)
    infer_instance
  exact history_stage_smooth_descends C q (nativeFinalSection R k)
    (nativeFinalSection_projection R k) (Fin.last _) (baseStructure R k)

/-- The genuine ORIGINAL singular ideal on the SAME actual descended principalized endpoint. -/
def nativePrincipalizedOriginalIdeal : (nativeBasePrincipalizationHistory R k).last.IdealSheafData :=
  (Spec (.of R)).singIdeal.comap ((nativeBasePrincipalizationHistory R k).composite ≫
    (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R))

/-- Actual projection equations identify the genuine ORIGINAL ideal with its ONE native upstairs pullback. -/
theorem nativePrincipalizedOriginalIdeal_pullback :
    (nativePrincipalizedOriginalIdeal R k).comap (nativePrincipalizedProjection R k) =
      (paddedFinalOriginalSing R k).comap (nativeOriginalSingPrincipalizationHistory R k).composite := by
  rw [nativePrincipalizedOriginalIdeal,paddedFinalOriginalSing,← comap_comp,← comap_comp]
  apply congrArg (Spec (.of R)).singIdeal.comap
  calc
    nativePrincipalizedProjection R k ≫ ((nativeBasePrincipalizationHistory R k).composite ≫
        (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) =
      (nativePrincipalizedProjection R k ≫ (nativeBasePrincipalizationHistory R k).composite) ≫
        (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by simp [Category.assoc]
    _ = (nativeOriginalSingPrincipalizationHistory R k).composite ≫ paddedFinalProjection R k ≫
        (nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by
      rw [nativePrincipalizedProjection_over,Category.assoc]
    _ = (nativeOriginalSingPrincipalizationHistory R k).composite ≫ (nativePaddedHistory R k).composite ≫
        envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by
      rw [← Category.assoc (paddedFinalProjection R k),paddedFinalProjection_over,Category.assoc]

/-- The specified genuine downstairs ORIGINAL ideal has the actual native SNC ideal as its pullback. -/
theorem nativePrincipalizedOriginalIdeal_snc_pullback :
    ((nativePrincipalizedOriginalIdeal R k).comap (nativePrincipalizedProjection R k)).IsIdealOfSncDivisor := by
  rw [nativePrincipalizedOriginalIdeal_pullback]
  exact nativeOriginalSingPrincipalization_isSNC R k
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualPrincipalizedEndpointGeometry
