import Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingSmoothNaturality

/-!
# SAME entire ORIGINAL strong history under actual smooth surjections

Source-first proof: `actual-global-strong-resolution-smooth-surjective-20261102.tex`.
Actual smooth ORIGINAL ideal transport and genuine endpoint/OWN zero
uniqueness derive the SAME BP clock, then the whole original cons history.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothSurjective

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity ActualGlobalDimensionClopenPartition
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalSeparationBlowupFunctoriality ActualGlobalPaddedSmoothComparison
  ActualGlobalOriginalSingPrincipalizationInput ActualGlobalPaddingPrincipalizationChoice
open ActualVariableOriginalSingPrincipalizationChoice (composite_hom_ext_of_flat)

theorem concat_eq_pullback_of_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : X.BlowUpSequence) (T : Y.BlowUpSequence) (U : S.last.BlowUpSequence) (V : T.last.BlowUpSequence)
    (hT : T = S.pullback f)
    (hV : V = U.pullback (eqToHom (congrArg Scheme.BlowUpSequence.last hT) ≫ S.pullbackLastHom f)) :
    T.concat V = (S.concat U).pullback f := by
  subst T
  rw [pullback_concat]
  apply congrArg (S.pullback f).concat
  simpa only [eqToHom_refl, Category.id_comp] using hV

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X] [IsNoetherian Y] [IsReduced Y]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (f : Y ⟶ X) [Smooth f] [Surjective f] [IsSeparated (f ≫ p)]

local notation "SY" => history (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "SX" => canonicalHistory p
local notation "AY" => canonicalBaseHistory (f ≫ p)
local notation "AX" => canonicalBaseHistory p
local notation "TY" => originalTriple (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "TX" => originalTriple p (paddingVariables p) (commonDimension p) (padding_rank p)
local notation "PY" => principalizationHistory (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "PX" => principalizationHistory p (paddingVariables p) (commonDimension p) (padding_rank p)
local notation "QY" => normalizedEndpointProjection (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "QX" => normalizedEndpointProjection p (paddingVariables p) (commonDimension p) (padding_rank p)
local notation "sY" => normalizedEndpointSection (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)
local notation "sX" => normalizedEndpointSection p (paddingVariables p) (commonDimension p) (padding_rank p)
local notation "CX" => ActualGlobalOriginalSingPrincipalizationHistoryDescent.basePrincipalizationHistory p
  (paddingVariables p) (commonDimension p) (padding_rank p)
local notation "CY" => ActualGlobalOriginalSingPrincipalizationHistoryDescent.basePrincipalizationHistory (f ≫ p)
  (paddingVariables (f ≫ p)) (commonDimension (f ≫ p)) (padding_rank (f ≫ p))

omit [IsReduced X] [CharZero k] [IsSeparated p] in
include p in
private theorem base_noetherian : IsNoetherian (separationSpace X) := by
  have : FiniteType p := inferInstance
  have : IsProper (separationProjection X) := ActualGlobalSeparationAffineCharts.separationProjection_isProper
  let g := separationStructure p
  have : LocallyOfFiniteType g := inferInstance
  have : QuasiCompact g := by dsimp only [g, separationStructure]; infer_instance
  exact g.isNoetherian_of_field

def baseEndpointMap : (AY).last ⟶ (AX).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (baseHistory_smooth_surjective p f)) ≫
    (AX).pullbackLastHom (separationMap p f)

theorem baseEndpoint_isPullback : IsPullback (baseEndpointMap p f) (AY).composite (AX).composite (separationMap p f) := by
  have := separationMap_smooth p f
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq AX (separationMap p f) AY
    (baseHistory_smooth_surjective p f)

theorem baseEndpoint_over : baseEndpointMap p f ≫ (AX).composite = (AY).composite ≫ separationMap p f :=
  (baseEndpoint_isPullback p f).w

theorem baseEndpoint_smooth : Smooth (baseEndpointMap p f) :=
  property_of_isPullback _ (baseEndpoint_isPullback p f) (separationMap_smooth p f)

def nativeEndpointMap : (SY).last ⟶ (SX).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (sourceHistory_eq_pullback p f)) ≫
    (SX).pullbackLastHom (comparisonMap p f)

theorem nativeEndpoint_isPullback : IsPullback (nativeEndpointMap p f) (SY).composite (SX).composite (comparisonMap p f) := by
  have := comparisonMap_smooth p f
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq SX (comparisonMap p f) SY
    (sourceHistory_eq_pullback p f)

theorem nativeEndpoint_over : nativeEndpointMap p f ≫ (SX).composite = (SY).composite ≫ comparisonMap p f :=
  (nativeEndpoint_isPullback p f).w

theorem nativeEndpoint_smooth : Smooth (nativeEndpointMap p f) :=
  property_of_isPullback _ (nativeEndpoint_isPullback p f) (comparisonMap_smooth p f)

theorem nativeEndpoint_surjective : Surjective (nativeEndpointMap p f) :=
  property_of_isPullback _ (nativeEndpoint_isPullback p f) (comparisonMap_surjective p f)

theorem nativeEndpoint_original :
    nativeEndpointMap p f ≫ ((SX).composite ≫ projection X (paddingVariables p) ≫ separationProjection X) =
      ((SY).composite ≫ projection Y (sourceVariables p f) ≫ separationProjection Y) ≫ f := by
  rw [← Category.assoc, nativeEndpoint_over, Category.assoc,
    ← Category.assoc (comparisonMap p f), comparisonMap_projection, Category.assoc,
    separationMap_over]
  simp only [Category.assoc]

theorem principalization_eq_pullback : PY = (PX).pullback (nativeEndpointMap p f) := by
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
  exact BP_pullback_of_surjective TX TY m (nativeEndpoint_surjective p f).1 ⟨hf, hI, hE⟩

theorem nativeEndpoint_projection : nativeEndpointMap p f ≫ QX = QY ≫ baseEndpointMap p f := by
  have : IsNoetherian (separationSpace X) := base_noetherian p
  have : Smooth QY := normalizedEndpointProjection_smooth (f ≫ p) (sourceVariables p f)
    (sourceDimension p f) (source_rank p f)
  have : Smooth (baseEndpointMap p f) := baseEndpoint_smooth p f
  apply composite_hom_ext_of_flat AX
  rw [Category.assoc, normalizedEndpointProjection_over, ← Category.assoc, nativeEndpoint_over,
    Category.assoc, comparisonMap_projection, Category.assoc, baseEndpoint_over,
    ← Category.assoc QY (AY).composite, normalizedEndpointProjection_over, Category.assoc]

theorem endpointSection_compatibility : sY ≫ nativeEndpointMap p f = baseEndpointMap p f ≫ sX := by
  apply (normalizedEndpoint_isPullback p (paddingVariables p) (commonDimension p) (padding_rank p)).hom_ext
  · rw [Category.assoc, nativeEndpoint_projection, ← Category.assoc,
      normalizedEndpointSection_projection, Category.id_comp, Category.assoc,
      normalizedEndpointSection_projection, Category.comp_id]
  · rw [Category.assoc, nativeEndpoint_over, ← Category.assoc,
      normalizedEndpointSection_original, Category.assoc, comparisonMap_zero,
      ← Category.assoc, ← baseEndpoint_over, Category.assoc,
      ← normalizedEndpointSection_original p (paddingVariables p) (commonDimension p) (padding_rank p),
      Category.assoc]

theorem basePrincipalization_smooth_surjective : CY = (CX).pullback (baseEndpointMap p f) := by
  calc
    CY = normalizedBasePrincipalizationHistory (f ≫ p) (sourceVariables p f)
        (sourceDimension p f) (source_rank p f) :=
      (normalizedBasePrincipalization_eq_canonical (f ≫ p) (sourceVariables p f)
        (sourceDimension p f) (source_rank p f)).symm
    _ = (PY).pullback sY := rfl
    _ = ((PX).pullback (nativeEndpointMap p f)).pullback sY :=
      congrArg (fun T => T.pullback sY) (principalization_eq_pullback p f)
    _ = (PX).pullback (sY ≫ nativeEndpointMap p f) := (pullback_comp _ _ _).symm
    _ = (PX).pullback (baseEndpointMap p f ≫ sX) := by rw [endpointSection_compatibility]
    _ = ((PX).pullback sX).pullback (baseEndpointMap p f) := pullback_comp _ _ _
    _ = (CX).pullback (baseEndpointMap p f) := rfl

theorem canonicalOriginalHistory_smooth_surjective :
    ActualGlobalMixedDimensionResolution.canonicalOriginalHistory (f ≫ p) =
      (ActualGlobalMixedDimensionResolution.canonicalOriginalHistory p).pullback f := by
  have ht : (AY).concat CY = ((AX).concat CX).pullback (separationMap p f) :=
    concat_eq_pullback_of_eq (separationMap p f) AX AY CX CY (baseHistory_smooth_surjective p f)
      (basePrincipalization_smooth_surjective p f)
  exact ActualGlobalWeakResolutionSmoothSurjective.cons_eq_pullback_of_ideal_eq f
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X) (ActualGlobalDimensionSeparationIdeal.separationIdeal Y)
    ((AX).concat CX) ((AY).concat CY) (ActualGlobalSeparationSmoothNaturality.separationIdeal_smooth p f) ht

end
end Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothSurjective
