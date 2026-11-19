import Hironaka.Resolution.Algebraic.ActualGlobalPaddedNativeInput
import Hironaka.Resolution.Algebraic.ActualRelativeAffineHistoryDescent
import Hironaka.Resolution.Algebraic.ActualDescendedHistorySmoothEndpoint

/-!
# Exact descent of the same whole native history to the actual global blowup

Source-first proof: `actual-global-native-history-descent-20261102.tex`.
The one actual global native input, genuine translations and ALG8 induction
derive exact own-section history descent and actual endpoint smoothness.
Original-singular principalization and genuine smooth/field compatibility
remain open; no compatibility milestone is closed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalNativeHistoryDescent

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

def history : (envelope X V).BlowUpSequence :=
  nativeResolutionFamily k (variableEnvelope p V N hN)

theorem history_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (variableEnvelope p V N hN).obj (history p V N hN) :=
  (Classical.choose_spec exists_functorial_resolution).1 k (variableEnvelope p V N hN)

private def translation (v : ∀ d, V d → ℤ) : envelope X V ⟶ envelope X V :=
  clopenTranslation V (pieceFamily X) v

private instance translation_isIso (v : ∀ d, V d → ℤ) : IsIso (translation V v) := by
  dsimp only [translation, clopenTranslation]
  infer_instance

omit [IsReduced X] [∀ d, Finite (V d)] in
private theorem translation_projection (v : ∀ d, V d → ℤ) :
    translation V v ≫ projection X V = projection X V := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc, translation, clopenTranslation, Sigma.ι_map, Category.assoc,
    projection, Sigma.ι_desc, ← Category.assoc]
  rw [affineTranslation_projection]

private def translationInput (v : ∀ d, V d → ℤ) :
    variableEnvelope p V N hN ⟶ variableEnvelope p V N hN :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (translation V v) (by
    change translation V v ≫ envelopeStructure p V = envelopeStructure p V
    rw [envelopeStructure, ← Category.assoc, translation_projection]))

theorem history_translation (v : ∀ d, V d → ℤ) :
    history p V N hN = (history p V N hN).pullback (clopenTranslation V (pieceFamily X) v) := by
  have hs : Smooth (HasUnderlyingScheme.hom (translationInput p V N hN v)) := by
    change Smooth (translation V v)
    infer_instance
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (translationInput p V N hN v) hs (surjective_of_isIso (translation V v))

def baseHistory : (ActualGlobalDimensionClopenPartition.separationSpace X).BlowUpSequence :=
  (history p V N hN).pullback (zeroSection X V)

theorem history_descends : history p V N hN = (baseHistory p V N hN).pullback (projection X V) := by
  let B := pieceFamily X
  let S : (∐ fun d => AffineSpace (V d) (B d)).BlowUpSequence := history p V N hN
  have h := clopen_relative_history_descends V B k (pieceStructure p) S (history_translation p V N hN)
  have hproj : clopenProjection V B ≫ piecesDesc X = projection X V := by
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc, clopenProjection, Sigma.ι_map, Category.assoc, piecesDesc, Sigma.ι_desc,
      projection, Sigma.ι_desc]
  have hsection : zeroSection X V = inv (piecesDesc X) ≫ clopenZeroSection V B := rfl
  have hc : projection X V ≫ zeroSection X V = clopenProjection V B ≫ clopenZeroSection V B := by
    rw [← hproj, hsection, Category.assoc, ← Category.assoc (piecesDesc X),
      IsIso.hom_inv_id, Category.id_comp]
  change history p V N hN = ((history p V N hN).pullback (zeroSection X V)).pullback (projection X V)
  rw [← pullback_comp] at h ⊢
  rw [hc]
  exact h

theorem baseHistory_length : (baseHistory p V N hN).length = (history p V N hN).length :=
  length_pullback _ _

def separationStructure : ActualGlobalDimensionClopenPartition.separationSpace X ⟶ Spec (.of k) :=
  ActualGlobalDimensionClopenPartition.separationProjection X ≫ p

instance separationStructure_locallyOfFiniteType : LocallyOfFiniteType (separationStructure p) := by
  have : IsProper (ActualGlobalDimensionClopenPartition.separationProjection X) :=
    ActualGlobalSeparationAffineCharts.separationProjection_isProper (X := X)
  dsimp [separationStructure]
  infer_instance

theorem baseHistory_smooth : Smooth ((baseHistory p V N hN).composite ≫ separationStructure p) := by
  let A := baseHistory p V N hN
  let q := projection X V
  have : IsLocallyNoetherian (ActualGlobalDimensionClopenPartition.separationSpace X) :=
    LocallyOfFiniteType.isLocallyNoetherian (separationStructure p)
  have : IsProper A.composite := A.isProper_composite
  have : Smooth q := projection_smooth X V
  have : IsAffineHom q := projection_affine X V
  have hwhole : history p V N hN = A.pullback q := history_descends p V N hN
  have : Smooth ((A.pullback q).composite ≫ q ≫ separationStructure p) := by
    change Smooth ((A.pullback q).composite ≫ (variableEnvelope p V N hN).obj.hom)
    rw [← hwhole]
    exact (history_isStrongResolution p V N hN).smooth
  have : Smooth ((A.pullback q).stageMap (A.pullbackStageIdx q (Fin.last _)) ≫
      q ≫ separationStructure p) := by
    rw [pullbackStageIdx_last]
    change Smooth ((A.pullback q).composite ≫ q ≫ separationStructure p)
    infer_instance
  have : LocallyOfFinitePresentation (A.stageMap (Fin.last _) ≫ separationStructure p) := by
    change LocallyOfFinitePresentation (A.composite ≫ separationStructure p)
    infer_instance
  exact ActualDescendedHistorySmoothEndpoint.history_stage_smooth_descends A q
    (zeroSection X V) (zeroSection_projection X V) (Fin.last _) (separationStructure p)

abbrev canonicalHistory := history p (paddingVariables p) (commonDimension p) (padding_rank p)

abbrev canonicalBaseHistory := baseHistory p (paddingVariables p) (commonDimension p) (padding_rank p)

theorem canonicalHistory_descends : canonicalHistory p =
    (canonicalBaseHistory p).pullback (envelopeProjection p) :=
  history_descends p (paddingVariables p) (commonDimension p) (padding_rank p)

theorem canonicalBaseHistory_smooth : Smooth ((canonicalBaseHistory p).composite ≫ separationStructure p) :=
  baseHistory_smooth p (paddingVariables p) (commonDimension p) (padding_rank p)

end
end Hironaka.Resolution.Algebraic.ActualGlobalNativeHistoryDescent
