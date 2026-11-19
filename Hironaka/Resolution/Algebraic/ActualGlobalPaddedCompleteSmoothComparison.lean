import Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothSurjective

/-!
# SAME complete padded F+BP under arbitrary original smooth morphisms

Source-first proof: `actual-global-padded-complete-smooth-comparison-20261102.tex`.
Native erasure endpoint isomorphism and actual ORIGINAL ideal transport
derive genuine whole padded chronological comparison, without clock matching.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalPaddedCompleteSmoothComparison

noncomputable section

theorem concat_eq_eraseEmpty_pullback_of_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : X.BlowUpSequence) (T : Y.BlowUpSequence) (U : S.last.BlowUpSequence) (V : T.last.BlowUpSequence)
    (hT : T = (S.pullback f).eraseEmpty)
    (hV : V = (U.pullback (eqToHom (congrArg Scheme.BlowUpSequence.last hT) ≫
      (S.pullback f).eraseEmptyLastHom ≫ S.pullbackLastHom f)).eraseEmpty) :
    T.concat V = ((S.concat U).pullback f).eraseEmpty := by
  subst T
  simp only [eqToHom_refl, Category.id_comp] at hV
  rw [pullback_concat, eraseEmpty_concat]
  apply congrArg (S.pullback f).eraseEmpty.concat
  rw [hV, ← eraseEmpty_pullback_of_flat_surjective _ (S.pullback f).eraseEmptyLastHom
    (surjective_of_isIso _), ← pullback_comp]

open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity ActualGlobalDimensionClopenPartition
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalSeparationBlowupFunctoriality ActualGlobalPaddedSmoothComparison
  ActualGlobalOriginalSingPrincipalizationInput ActualPaddedEnvelopeNativeTranslations

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X] [IsNoetherian Y] [IsReduced Y]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (f : Y ⟶ X) [Smooth f] [IsSeparated (f ≫ p)]

local notation "SY" => history (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "SX" => canonicalHistory p
local notation "TY" => originalTriple (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "TX" => originalTriple p (paddingVariables p) (commonDimension p) (padding_rank p)
local notation "PY" => principalizationHistory (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "PX" => principalizationHistory p (paddingVariables p) (commonDimension p) (padding_rank p)

private def inputMap : sourceInput p f ⟶ paddedEnvelope p :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (comparisonMap p f) (by
    change comparisonMap p f ≫ envelopeStructure p (paddingVariables p) =
      envelopeStructure (f ≫ p) (sourceVariables p f)
    rw [envelopeStructure, ← Category.assoc, comparisonMap_projection, Category.assoc,
      ← Category.assoc (separationMap p f), separationMap_over, Category.assoc]
    rfl))

theorem sourceHistory_eq_eraseEmpty_pullback : SY = ((SX).pullback (comparisonMap p f)).eraseEmpty := by
  have hs : Smooth (HasUnderlyingScheme.hom (inputMap p f)) := comparisonMap_smooth p f
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_eraseEmpty_pullback (inputMap p f) hs

def nativeEndpointMap : (SY).last ⟶ (SX).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (sourceHistory_eq_eraseEmpty_pullback p f)) ≫
    ((SX).pullback (comparisonMap p f)).eraseEmptyLastHom ≫ (SX).pullbackLastHom (comparisonMap p f)

theorem nativeEndpoint_over : nativeEndpointMap p f ≫ (SX).composite = (SY).composite ≫ comparisonMap p f := by
  let S := (SX).pullback (comparisonMap p f)
  have he : ∀ (T : (ActualGlobalVariablePaddingGeometry.envelope Y (sourceVariables p f)).BlowUpSequence)
      (h : T = S.eraseEmpty),
      (eqToHom (congrArg Scheme.BlowUpSequence.last h) ≫ S.eraseEmptyLastHom ≫
        (SX).pullbackLastHom (comparisonMap p f)) ≫ (SX).composite = T.composite ≫ comparisonMap p f := by
    intro T h
    subst T
    rw [eqToHom_refl, Category.id_comp, Category.assoc,
      pullbackLastHom_comp_composite, ← Category.assoc, eraseEmptyLastHom_comp_composite]
  exact he SY (sourceHistory_eq_eraseEmpty_pullback p f)

theorem nativeEndpoint_smooth : Smooth (nativeEndpointMap p f) := by
  have := comparisonMap_smooth p f
  have : Smooth ((SX).pullbackLastHom (comparisonMap p f)) :=
    property_of_isPullback _ (ActualFinalClopenProductPresentation.lastStage_isPullback (SX) (comparisonMap p f))
      (inferInstance : Smooth (comparisonMap p f))
  dsimp only [nativeEndpointMap]
  infer_instance

theorem nativeEndpoint_original :
    nativeEndpointMap p f ≫ ((SX).composite ≫ projection X (paddingVariables p) ≫ separationProjection X) =
      ((SY).composite ≫ projection Y (sourceVariables p f) ≫ separationProjection Y) ≫ f := by
  rw [← Category.assoc, nativeEndpoint_over, Category.assoc,
    ← Category.assoc (comparisonMap p f), comparisonMap_projection, Category.assoc,
    separationMap_over]
  simp only [Category.assoc]

theorem principalization_eq_eraseEmpty_pullback : PY = ((PX).pullback (nativeEndpointMap p f)).eraseEmpty := by
  let m := nativeEndpointMap p f
  have : Smooth m := nativeEndpoint_smooth p f
  have hf : m ≫ ((TX).X.left ↘ Spec (.of k)) = (TY).X.left ↘ Spec (.of k) := by
    change m ≫ ((SX).composite ≫ projection X (paddingVariables p) ≫ separationProjection X ≫ p) =
      (SY).composite ≫ projection Y (sourceVariables p f) ≫ separationProjection Y ≫ (f ≫ p)
    simpa only [Category.assoc] using congrArg (fun g => g ≫ p) (nativeEndpoint_original p f)
  have hI : (TY).I = (TX).I.comap m := by
    change originalIdeal (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f) =
      (originalIdeal p (paddingVariables p) (commonDimension p) (padding_rank p)).comap m
    rw [originalIdeal, originalIdeal, ← ActualGlobalOriginalSingSmoothNaturality.singIdeal_smooth p f,
      ← comap_comp, ← comap_comp]
    apply congrArg X.singIdeal.comap
    exact (nativeEndpoint_original p f).symm
  have hE : (TY).E = (TX).E.comap m := (empty_comap m).symm
  exact BP_pullback_eraseEmpty TX TY m ⟨hf, hI, hE⟩

theorem paddedCompleteHistory_eq_eraseEmpty_pullback : (SY).concat PY =
    (((SX).concat PX).pullback (comparisonMap p f)).eraseEmpty :=
  concat_eq_eraseEmpty_pullback_of_eq (comparisonMap p f) SX SY PX PY
    (sourceHistory_eq_eraseEmpty_pullback p f) (principalization_eq_eraseEmpty_pullback p f)

end
end Hironaka.Resolution.Algebraic.ActualGlobalPaddedCompleteSmoothComparison
