import Hironaka.Resolution.Algebraic.ActualFinalClopenProductPresentation

/-!
# Canonical descent of ONE actual ORIGINAL-singular principalization history

Source-first proof: `actual-original-sing-principalization-history-descent-20261102.tex`.
All translations and the final product/zero section are actual constructed geometry.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualOriginalSingPrincipalizationHistoryDescent

noncomputable section
open ActualPaddedEnvelopeNativeTranslations

private theorem translation_coord (V : Type u) (X : Scheme.{u}) (v : V → ℤ) (i : V) :
    (affineTranslation V X v).hom.appTop (AffineSpace.coord X i) =
      AffineSpace.coord X i + (v i : Γ(AffineSpace V X,⊤)) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Actual relative coordinate translations are natural for ANY actual base morphism. -/
theorem affineTranslation_map_naturality (V : Type u) {X Y : Scheme.{u}}
    (f : Y ⟶ X) (v : V → ℤ) :
    (affineTranslation V Y v).hom ≫ AffineSpace.map V f =
      AffineSpace.map V f ≫ (affineTranslation V X v).hom := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc,AffineSpace.map_over,← Category.assoc,affineTranslation_projection,
      Category.assoc,affineTranslation_projection,AffineSpace.map_over]
  · intro i
    simp only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,AffineSpace.map_appTop_coord,
      translation_coord,map_add,map_intCast]

open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces
  ActualDimensionGroupPaddedCover ActualRelativeAffineHistoryDescent
  ActualPaddedNativePrincipalizationInput ActualPaddedPrincipalizationTranslationEquivariance
  ActualFinalClopenProductPresentation

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

private abbrev basePiece (d : dimensionIndex R) : Scheme.{u} :=
  restrictedEndpoint (dimensionPartOpen R) (nativeBaseHistory R k) d

private abbrev productSource : Scheme.{u} :=
  ∐ fun d : dimensionIndex R => AffineSpace (paddingVariables R k d) (basePiece R k d)

private abbrev baseDesc : (∐ basePiece R k) ⟶ (nativeBaseHistory R k).last :=
  restrictedEndpointsDesc (dimensionPartOpen R) (nativeBaseHistory R k)

private instance baseDesc_isIso : IsIso (baseDesc R k) :=
  restrictedEndpointsDesc_isIso (dimensionPartOpen R) (nativeBaseHistory R k)
    (dimension_group_clopen_partition R).1 (dimension_group_clopen_partition R).2.1

private theorem productTranslation_originalMap
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    clopenTranslation (paddingVariables R k) (basePiece R k) v ≫
        finalProductOriginalMap (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k) =
      finalProductOriginalMap (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k) ≫
        envelopeTranslation R k v := by
  change Limits.Sigma.map (fun d => (affineTranslation (paddingVariables R k d)
      (basePiece R k d) (v d)).hom) ≫
      Limits.Sigma.map (fun d => AffineSpace.map (paddingVariables R k d)
        ((nativeBaseHistory R k).pullback (dimensionPartOpen R d).ι).composite) =
    Limits.Sigma.map (fun d => AffineSpace.map (paddingVariables R k d)
        ((nativeBaseHistory R k).pullback (dimensionPartOpen R d).ι).composite) ≫
      Limits.Sigma.map (fun d => (affineTranslation (paddingVariables R k d)
        (dimensionPartOpen R d).toScheme (v d)).hom)
  rw [Limits.Sigma.map_comp_map,Limits.Sigma.map_comp_map]
  apply congrArg Limits.Sigma.map
  funext d
  exact affineTranslation_map_naturality _ _ _

/-- The ONE actual principalization, transported to its actual current product presentation. -/
def productPrincipalizationHistory : (productSource R k).BlowUpSequence :=
  (nativeOriginalSingPrincipalizationHistory R k).pullback (nativeFinalProductIso R k).hom

/-- Genuine final product translations preserve this SAME literal principalization clock. -/
theorem productPrincipalizationHistory_invariant
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    productPrincipalizationHistory R k = (productPrincipalizationHistory R k).pullback
      (clopenTranslation (paddingVariables R k) (basePiece R k) v) := by
  let e := nativeFinalProductIso R k
  let t := clopenTranslation (paddingVariables R k) (basePiece R k) v
  have : IsIso t := by
    change IsIso (Limits.Sigma.map (fun d => (affineTranslation (paddingVariables R k d)
      (basePiece R k d) (v d)).hom))
    infer_instance
  let g := e.inv ≫ t ≫ e.hom
  have : IsIso g := by dsimp only [g]; infer_instance
  let f := (nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
    affineBlowUp.π (dimensionSeparationIdeal R)
  let r := finalProductOriginalMap (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k)
  have he : e.hom ≫ f = r ≫ envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by
    rw [show e.hom ≫ f = (e.hom ≫ (nativePaddedHistory R k).composite) ≫
      envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) from (Category.assoc _ _ _).symm]
    rw [nativeFinalProductIso_original_map]
  have hg : g ≫ f = f := by
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ (g ≫ f) = t ≫ e.hom ≫ f := by simp [g,Category.assoc]
      _ = t ≫ r ≫ envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by rw [he]
      _ = r ≫ envelopeTranslation R k v ≫ envelopeProjection R k ≫
          affineBlowUp.π (dimensionSeparationIdeal R) := by
        rw [← Category.assoc t r,productTranslation_originalMap,Category.assoc]
      _ = r ≫ envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) := by
        rw [← Category.assoc (envelopeTranslation R k v),envelopeTranslation_projection]
      _ = e.hom ≫ f := he.symm
  have hBP := principalization_eq_pullback_of_original_projection R k g hg
  have ht : e.hom ≫ g = t ≫ e.hom := by simp [g]
  have h := congrArg (fun S => S.pullback e.hom) hBP
  rw [← pullback_comp,ht,pullback_comp] at h
  exact h

private theorem clopenZeroSection_projection :
    clopenZeroSection (paddingVariables R k) (basePiece R k) ≫
      clopenProjection (paddingVariables R k) (basePiece R k) = 𝟙 (∐ basePiece R k) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc,clopenZeroSection,Sigma.ι_map,Category.assoc,clopenProjection,Sigma.ι_map,
    ← Category.assoc,AffineSpace.homOfVector_over,Category.id_comp,Category.comp_id]

/-- Actual final zero section, constructed through the actual SAME product and base isomorphisms. -/
def nativeFinalSection : (nativeBaseHistory R k).last ⟶ (nativePaddedHistory R k).last :=
  inv (baseDesc R k) ≫ clopenZeroSection (paddingVariables R k) (basePiece R k) ≫
    (nativeFinalProductIso R k).hom

/-- This genuine actual final section retracts the SAME actual padded final projection. -/
theorem nativeFinalSection_projection :
    nativeFinalSection R k ≫ paddedFinalProjection R k = 𝟙 (nativeBaseHistory R k).last := by
  rw [nativeFinalSection,Category.assoc,Category.assoc,nativeFinalProductIso_projection]
  change inv (baseDesc R k) ≫ clopenZeroSection (paddingVariables R k) (basePiece R k) ≫
    clopenProjection (paddingVariables R k) (basePiece R k) ≫ baseDesc R k = _
  rw [← Category.assoc (clopenZeroSection _ _),clopenZeroSection_projection,Category.id_comp,
    IsIso.inv_hom_id]

/-- The canonical base principalization is the ONE actual history's OWN actual final-section pullback. -/
def nativeBasePrincipalizationHistory : (nativeBaseHistory R k).last.BlowUpSequence :=
  (nativeOriginalSingPrincipalizationHistory R k).pullback (nativeFinalSection R k)

/-- The WHOLE ONE original-singular principalization descends on the SAME clock to the SAME base. -/
theorem nativePrincipalization_canonical_history_descends :
    nativeOriginalSingPrincipalizationHistory R k =
      (nativeBasePrincipalizationHistory R k).pullback (paddedFinalProjection R k) := by
  let e := nativeFinalProductIso R k
  let q := clopenProjection (paddingVariables R k) (basePiece R k)
  let s := clopenZeroSection (paddingVariables R k) (basePiece R k)
  have hcan := clopen_relative_history_descends (paddingVariables R k) (basePiece R k) k
    (fun d => ( (nativeBaseHistory R k).pullback (dimensionPartOpen R d).ι).composite ≫
      (pieceAlgScheme R k d).hom) (productPrincipalizationHistory R k)
    (productPrincipalizationHistory_invariant R k)
  have hep : e.hom ≫ paddedFinalProjection R k = q ≫ baseDesc R k :=
    nativeFinalProductIso_projection R k
  have hinv : e.inv ≫ q = paddedFinalProjection R k ≫ inv (baseDesc R k) := by
    symm
    simpa only [Category.assoc,Iso.inv_hom_id_assoc,IsIso.hom_inv_id,Category.comp_id] using
      (congrArg (fun h => e.inv ≫ h ≫ inv (baseDesc R k)) hep)
  calc
    nativeOriginalSingPrincipalizationHistory R k = (productPrincipalizationHistory R k).pullback e.inv := by
      rw [productPrincipalizationHistory,← pullback_comp,Iso.inv_hom_id,pullback_id]
    _ = (((productPrincipalizationHistory R k).pullback s).pullback q).pullback e.inv :=
      congrArg (fun S => S.pullback e.inv) hcan
    _ = (nativeBasePrincipalizationHistory R k).pullback (paddedFinalProjection R k) := by
      simp only [productPrincipalizationHistory,nativeBasePrincipalizationHistory,← pullback_comp]
      apply congrArg ((nativeOriginalSingPrincipalizationHistory R k).pullback)
      change e.inv ≫ q ≫ s ≫ e.hom = paddedFinalProjection R k ≫
        inv (baseDesc R k) ≫ s ≫ e.hom
      rw [← Category.assoc e.inv q,hinv,Category.assoc]
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualOriginalSingPrincipalizationHistoryDescent
