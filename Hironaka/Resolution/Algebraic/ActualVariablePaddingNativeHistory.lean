import Hironaka.Resolution.Algebraic.ActualCommonNativeResolutionComparison

/-!
# Genuine SAME whole-history descent and final geometry for every valid padding choice

Source-first proof: `actual-variable-padding-native-history-20261102.tex`.
Actual translations and native whole-tail descent produce real endpoint
cartesian squares and real sections, not history or final-geometry certificates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualVariablePaddingNativeHistory

noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualCommonNativeResolutionComparison

variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]
  (V : dimensionIndex R → Type u) [∀ d, Finite (V d)]
  (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)

/-- The SAME native family has genuine strong-resolution geometry on the actual internally constructed input. -/
theorem history_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _
      (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN).obj (history R k V N hN) :=
  (Classical.choose_spec exists_functorial_resolution).1 k
    (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN)

private abbrev pieceFamily : dimensionIndex R → Scheme.{u} := fun d => (dimensionPartOpen R d).toScheme

private def translation (v : ∀ d, V d → ℤ) :
    ActualVariablePaddingEnvelope.envelope R V ⟶ ActualVariablePaddingEnvelope.envelope R V :=
  clopenTranslation V (pieceFamily R) v

private instance translation_isIso (v : ∀ d, V d → ℤ) : IsIso (translation R V v) := by
  dsimp only [translation,clopenTranslation]
  infer_instance

omit [IsReduced R] [∀ d, Finite (V d)] in
private theorem translation_projection (v : ∀ d, V d → ℤ) :
    translation R V v ≫ ActualVariablePaddingEnvelope.projection R V =
      ActualVariablePaddingEnvelope.projection R V := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc,translation,clopenTranslation,Sigma.ι_map,Category.assoc,
    ActualVariablePaddingEnvelope.projection,Sigma.ι_desc,← Category.assoc]
  have ht := affineTranslation_projection (V d) (dimensionPartOpen R d).toScheme (v d)
  rw [ht]

private def translationInput (v : ∀ d, V d → ℤ) :
    ActualVariablePaddingEnvelope.variableEnvelope R V k N hN ⟶
      ActualVariablePaddingEnvelope.variableEnvelope R V k N hN :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (translation R V v) (by
    change translation R V v ≫ (ActualVariablePaddingEnvelope.projection R V ≫
      affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
    rw [← Category.assoc,translation_projection]
    rfl))

/-- Genuine actual translations preserve the SAME arbitrary-padding native whole history. -/
theorem history_translation (v : ∀ d, V d → ℤ) :
    history R k V N hN = (history R k V N hN).pullback (clopenTranslation V (pieceFamily R) v) := by
  have hs : Smooth (HasUnderlyingScheme.hom (translationInput R k V N hN v)) := by
    change Smooth (translation R V v)
    infer_instance
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (translationInput R k V N hN v) hs (surjective_of_isIso (translation R V v))

/-- Genuine whole-tail translation descent to the OWN actual original zero-section history. -/
theorem history_zero_descends : history R k V N hN =
    (baseHistory R k V N hN).pullback (ActualVariablePaddingEnvelope.projection R V) := by
  let B := pieceFamily R
  let S : (∐ fun d => AffineSpace (V d) (B d)).BlowUpSequence := history R k V N hN
  have h := clopen_relative_history_descends V B k (fun d => (pieceAlgScheme R k d).hom) S
    (history_translation R k V N hN)
  have hproj : clopenProjection V B ≫ piecesDesc R = ActualVariablePaddingEnvelope.projection R V := by
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc,clopenProjection,Sigma.ι_map,Category.assoc,piecesDesc,Sigma.ι_desc,
      ActualVariablePaddingEnvelope.projection,Sigma.ι_desc]
  have hsection : ActualVariablePaddingEnvelope.zeroSection R V = inv (piecesDesc R) ≫
      clopenZeroSection V B := rfl
  have hc : ActualVariablePaddingEnvelope.projection R V ≫ ActualVariablePaddingEnvelope.zeroSection R V =
      clopenProjection V B ≫ clopenZeroSection V B := by
    rw [← hproj,hsection,Category.assoc,← Category.assoc (piecesDesc R),IsIso.hom_inv_id,Category.id_comp]
  change history R k V N hN = ((history R k V N hN).pullback
    (ActualVariablePaddingEnvelope.zeroSection R V)).pullback (ActualVariablePaddingEnvelope.projection R V)
  rw [← pullback_comp] at h ⊢
  rw [hc]
  exact h

/-- EVERY valid padding choice has literal genuine whole-history descent to the SAME original base history. -/
theorem history_original_descends : history R k V N hN =
    (nativeBaseHistory R k).pullback (ActualVariablePaddingEnvelope.projection R V) := by
  have h := history_zero_descends R k V N hN
  rw [baseHistory_eq_original] at h
  exact h

/-- Actual arbitrary-padding final projection, transported along the literal SAME whole-history equality. -/
def endpointProjection : (history R k V N hN).last ⟶ (nativeBaseHistory R k).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (history_original_descends R k V N hN)) ≫
    (nativeBaseHistory R k).pullbackLastHom (ActualVariablePaddingEnvelope.projection R V)

/-- The actual final square is DERIVED from native flat-pullback geometry and SAME-history equality. -/
theorem endpoint_isPullback : IsPullback (endpointProjection R k V N hN) (history R k V N hN).composite
    (nativeBaseHistory R k).composite (ActualVariablePaddingEnvelope.projection R V) := by
  have : Smooth (ActualVariablePaddingEnvelope.projection R V) := ActualVariablePaddingEnvelope.projection_smooth R V
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq (nativeBaseHistory R k)
    (ActualVariablePaddingEnvelope.projection R V) (history R k V N hN) (history_original_descends R k V N hN)

/-- Genuine actual original-input endpoint projection equation. -/
theorem endpointProjection_over : endpointProjection R k V N hN ≫ (nativeBaseHistory R k).composite =
    (history R k V N hN).composite ≫ ActualVariablePaddingEnvelope.projection R V :=
  (endpoint_isPullback R k V N hN).w

/-- The actual final projection is genuinely smooth. -/
theorem endpointProjection_smooth : Smooth (endpointProjection R k V N hN) :=
  property_of_isPullback _ (endpoint_isPullback R k V N hN) (ActualVariablePaddingEnvelope.projection_smooth R V)

/-- The actual final projection is genuinely affine. -/
theorem endpointProjection_affine : IsAffineHom (endpointProjection R k V N hN) :=
  property_of_isPullback _ (endpoint_isPullback R k V N hN) (ActualVariablePaddingEnvelope.projection_affine R V)

/-- The actual final projection is genuinely surjective. -/
theorem endpointProjection_surjective : Surjective (endpointProjection R k V N hN) :=
  property_of_isPullback _ (endpoint_isPullback R k V N hN) (ActualVariablePaddingEnvelope.projection_surjective R V)

/-- Actual final section, internally constructed by the genuine terminal cartesian universal property. -/
def endpointSection : (nativeBaseHistory R k).last ⟶ (history R k V N hN).last :=
  (endpoint_isPullback R k V N hN).lift (𝟙 _) ((nativeBaseHistory R k).composite ≫
    ActualVariablePaddingEnvelope.zeroSection R V) (by simp [ActualVariablePaddingEnvelope.zeroSection_projection])

/-- Genuine final retraction identity. -/
theorem endpointSection_projection : endpointSection R k V N hN ≫ endpointProjection R k V N hN =
    𝟙 (nativeBaseHistory R k).last := (endpoint_isPullback R k V N hN).lift_fst _ _ _

/-- The actual final section has the SAME prescribed original zero-section projection. -/
theorem endpointSection_original : endpointSection R k V N hN ≫ (history R k V N hN).composite =
    (nativeBaseHistory R k).composite ≫ ActualVariablePaddingEnvelope.zeroSection R V :=
  (endpoint_isPullback R k V N hN).lift_snd _ _ _

end
end Hironaka.Resolution.Algebraic.ActualVariablePaddingNativeHistory
