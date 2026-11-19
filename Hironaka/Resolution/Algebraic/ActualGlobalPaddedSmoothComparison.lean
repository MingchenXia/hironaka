import Hironaka.Resolution.Algebraic.ActualClopenPaddedMap

/-!
# Genuine global pure padded comparison under original smooth maps

Source-first proof: `actual-global-padded-smooth-comparison-20261102.tex`.
Actual original geometry derives the pure inputs, padded smooth/SURJ map,
BOTH original zeros, and exact SAME-family whole-clock base comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalPaddedSmoothComparison

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalDimensionClopenPartition ActualGlobalPaddedNativeInput
  ActualGlobalVariablePaddingGeometry ActualGlobalNativeHistoryDescent
  ActualGlobalSeparationBlowupFunctoriality

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X] [IsNoetherian Y] [IsReduced Y]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (f : Y ⟶ X) [Smooth f] [IsSeparated (f ≫ p)]

def sourceDimension : ℕ := commonDimension p + commonDimension (f ≫ p)

abbrev sourceVariables (e : dimensionIndex Y) : Type u :=
  ULift.{u} (Fin (sourceDimension p f - dimensionNat (f ≫ p) e))

omit [IsReduced X] [IsReduced Y] [CharZero k] [IsSeparated p] [IsSeparated (f ≫ p)] in
theorem source_rank (e : dimensionIndex Y) :
    dimensionNat (f ≫ p) e + Nat.card (sourceVariables p f e) = sourceDimension p f := by
  simp only [sourceVariables, Nat.card_ulift, Nat.card_fin]
  apply Nat.add_sub_of_le
  have h := commonDimension_ge (f ≫ p) e
  dsimp only [sourceDimension]
  omega

abbrev sourceInput : ReducedEquidimensionalScheme k :=
  variableEnvelope (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)

omit [IsReduced X] [IsReduced Y] [CharZero k] [IsSeparated p] [IsSeparated (f ≫ p)] in
theorem coordinateBound (a : dimensionIndex Y × dimensionIndex X) :
    commonDimension p - dimensionNat p a.2 ≤ sourceDimension p f - dimensionNat (f ≫ p) a.1 := by
  have h := commonDimension_ge (f ≫ p) a.1
  dsimp only [sourceDimension]
  omega

def keep (a : dimensionIndex Y × dimensionIndex X) : paddingVariables p a.2 → sourceVariables p f a.1 :=
  fun z => ULift.up (Fin.castLE (coordinateBound p f a) z.down)

omit [IsReduced X] [IsReduced Y] [CharZero k] [IsSeparated p] [IsSeparated (f ≫ p)] in
theorem keep_injective (a : dimensionIndex Y × dimensionIndex X) : Function.Injective (keep p f a) := by
  intro z w h
  apply ULift.ext
  exact Fin.ext (congrArg (fun z => z.down.val) h)

def comparisonMap : (sourceInput p f).obj.left ⟶ (paddedEnvelope p).obj.left :=
  ActualClopenPaddedMap.paddedMap (dimensionPartOpen Y) (dimensionPartOpen X) (separationMap p f)
    (sourceVariables p f) (paddingVariables p) (keep p f) (dimensionPartOpen_disjoint Y)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X)

theorem comparisonMap_projection : comparisonMap p f ≫ projection X (paddingVariables p) =
    projection Y (sourceVariables p f) ≫ separationMap p f :=
  ActualClopenPaddedMap.paddedMap_projection (dimensionPartOpen Y) (dimensionPartOpen X) (separationMap p f)
    (sourceVariables p f) (paddingVariables p) (keep p f) (dimensionPartOpen_disjoint Y)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X)

theorem comparisonMap_zero : zeroSection Y (sourceVariables p f) ≫ comparisonMap p f =
    separationMap p f ≫ zeroSection X (paddingVariables p) := by
  change ActualClopenPaddedMap.partitionZero (dimensionPartOpen Y) (sourceVariables p f)
      (dimensionPartOpen_cover Y) (dimensionPartOpen_disjoint Y) ≫ comparisonMap p f =
    separationMap p f ≫ ActualClopenPaddedMap.partitionZero (dimensionPartOpen X) (paddingVariables p)
      (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X)
  exact ActualClopenPaddedMap.paddedMap_zero (dimensionPartOpen Y) (dimensionPartOpen X) (separationMap p f)
    (sourceVariables p f) (paddingVariables p) (keep p f) (dimensionPartOpen_disjoint Y)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X) (dimensionPartOpen_cover Y)

theorem comparisonMap_smooth : Smooth (comparisonMap p f) := by
  have := separationMap_smooth p f
  exact ActualClopenPaddedMap.paddedMap_smooth (dimensionPartOpen Y) (dimensionPartOpen X) (separationMap p f)
    (sourceVariables p f) (paddingVariables p) (keep p f) (dimensionPartOpen_disjoint Y)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X) (keep_injective p f)

theorem comparisonMap_surjective [Surjective f] : Surjective (comparisonMap p f) := by
  have := separationMap_surjective p f
  exact ActualClopenPaddedMap.paddedMap_surjective (dimensionPartOpen Y) (dimensionPartOpen X) (separationMap p f)
    (sourceVariables p f) (paddingVariables p) (keep p f) (dimensionPartOpen_disjoint Y)
    (dimensionPartOpen_cover X) (dimensionPartOpen_disjoint X) (dimensionPartOpen_cover Y) (keep_injective p f)

private def inputMap : sourceInput p f ⟶ paddedEnvelope p :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (comparisonMap p f) (by
    change comparisonMap p f ≫ envelopeStructure p (paddingVariables p) =
      envelopeStructure (f ≫ p) (sourceVariables p f)
    rw [envelopeStructure, ← Category.assoc, comparisonMap_projection, Category.assoc,
      ← Category.assoc (separationMap p f), separationMap_over, Category.assoc]
    rfl))

theorem sourceHistory_eq_pullback [Surjective f] :
    history (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f) =
      (canonicalHistory p).pullback (comparisonMap p f) := by
  have hs : Smooth (HasUnderlyingScheme.hom (inputMap p f)) := comparisonMap_smooth p f
  exact (ActualPaddedEnvelopeNativeTranslations.nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (inputMap p f) hs (comparisonMap_surjective p f).1

theorem baseHistory_smooth_surjective [Surjective f] :
    canonicalBaseHistory (f ≫ p) = (canonicalBaseHistory p).pullback (separationMap p f) := by
  calc
    canonicalBaseHistory (f ≫ p) =
        (history (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)).pullback
          (zeroSection Y (sourceVariables p f)) :=
      (ActualGlobalPaddingResolutionChoice.baseHistory_eq_canonical (f ≫ p)
        (sourceVariables p f) (sourceDimension p f) (source_rank p f)).symm
    _ = ((canonicalHistory p).pullback (comparisonMap p f)).pullback (zeroSection Y (sourceVariables p f)) :=
      congrArg (fun S => S.pullback (zeroSection Y (sourceVariables p f))) (sourceHistory_eq_pullback p f)
    _ = (canonicalHistory p).pullback (zeroSection Y (sourceVariables p f) ≫ comparisonMap p f) :=
      (pullback_comp _ _ _).symm
    _ = (canonicalHistory p).pullback (separationMap p f ≫ zeroSection X (paddingVariables p)) := by
      rw [comparisonMap_zero]
    _ = ((canonicalHistory p).pullback (zeroSection X (paddingVariables p))).pullback (separationMap p f) :=
      pullback_comp _ _ _
    _ = (canonicalBaseHistory p).pullback (separationMap p f) := rfl

end
end Hironaka.Resolution.Algebraic.ActualGlobalPaddedSmoothComparison
