import Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingPrincipalizationHistoryDescent

/-!
# Genuine SNC of the ORIGINAL global singular support on the SAME endpoint

Source-first proof: `actual-global-principalized-endpoint-20261102.tex`.
Actual final split geometry reflects smoothness and the SAME fixed canonical
boundary's SNC.  No arbitrary-section SNC argument or substitute locus is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalPrincipalizedEndpoint

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingPrincipalizationInput ActualGlobalOriginalSingPrincipalizationHistoryDescent
  ActualPrincipalizationCanonicalBoundary ActualDescendedHistorySmoothEndpoint
  ActualGlobalDimensionClopenPartition

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

def baseStructure : (baseHistory p V N hN).last ⟶ Spec (.of k) :=
  (baseHistory p V N hN).composite ≫ separationStructure p

private instance baseStructure_smooth : Smooth (baseStructure p V N hN) := baseHistory_smooth p V N hN

private instance baseLocallyNoetherian : IsLocallyNoetherian (baseHistory p V N hN).last :=
  LocallyOfFiniteType.isLocallyNoetherian (baseStructure p V N hN)

private instance basePrincipalization_proper : IsProper (basePrincipalizationHistory p V N hN).composite :=
  (basePrincipalizationHistory p V N hN).isProper_composite

def principalizedProjection : (principalizationHistory p V N hN).last ⟶ (basePrincipalizationHistory p V N hN).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (principalizationHistory_descends p V N hN)) ≫
    (basePrincipalizationHistory p V N hN).pullbackLastHom (endpointProjection p V N hN)

theorem principalized_isPullback : IsPullback (principalizedProjection p V N hN)
    (principalizationHistory p V N hN).composite (basePrincipalizationHistory p V N hN).composite
      (endpointProjection p V N hN) := by
  have : Smooth (endpointProjection p V N hN) := endpointProjection_smooth p V N hN
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq
    (basePrincipalizationHistory p V N hN) (endpointProjection p V N hN)
    (principalizationHistory p V N hN) (principalizationHistory_descends p V N hN)

theorem principalizedProjection_over :
    principalizedProjection p V N hN ≫ (basePrincipalizationHistory p V N hN).composite =
      (principalizationHistory p V N hN).composite ≫ endpointProjection p V N hN :=
  (principalized_isPullback p V N hN).w

theorem principalizedProjection_smooth : Smooth (principalizedProjection p V N hN) :=
  property_of_isPullback _ (principalized_isPullback p V N hN) (endpointProjection_smooth p V N hN)

theorem principalizedProjection_affine : IsAffineHom (principalizedProjection p V N hN) :=
  property_of_isPullback _ (principalized_isPullback p V N hN) (endpointProjection_affine p V N hN)

theorem principalizedProjection_surjective : Surjective (principalizedProjection p V N hN) :=
  property_of_isPullback _ (principalized_isPullback p V N hN) (endpointProjection_surjective p V N hN)

def principalizedSection : (basePrincipalizationHistory p V N hN).last ⟶ (principalizationHistory p V N hN).last :=
  (principalized_isPullback p V N hN).lift (𝟙 _) ((basePrincipalizationHistory p V N hN).composite ≫
    endpointSection p V N hN) (by simp [Category.assoc, endpointSection_projection])

theorem principalizedSection_projection : principalizedSection p V N hN ≫ principalizedProjection p V N hN =
    𝟙 (basePrincipalizationHistory p V N hN).last := (principalized_isPullback p V N hN).lift_fst _ _ _

theorem paddedPrincipalization_smooth :
    Smooth ((principalizationHistory p V N hN).composite ≫ endpointStructure p V N hN) := by
  let T := originalTriple p V N hN
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have : SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k)) := hn
  change Smooth ((BP T).composite ≫ (T.X.left ↘ Spec (.of k)))
  exact IsSmooth.smooth_stageMap (n := n) (BP_isOrderGeSeq_zero T).1 (Fin.last _)

private theorem endpointProjection_structure : endpointProjection p V N hN ≫ baseStructure p V N hN =
    endpointStructure p V N hN := by
  change endpointProjection p V N hN ≫ ((baseHistory p V N hN).composite ≫ separationProjection X ≫ p) =
    (history p V N hN).composite ≫ projection X V ≫ separationProjection X ≫ p
  rw [← Category.assoc, endpointProjection_over, Category.assoc]

theorem principalizedBase_smooth :
    Smooth ((basePrincipalizationHistory p V N hN).composite ≫ baseStructure p V N hN) := by
  let C := basePrincipalizationHistory p V N hN
  let q := endpointProjection p V N hN
  have : Smooth q := endpointProjection_smooth p V N hN
  have : IsAffineHom q := endpointProjection_affine p V N hN
  have : Smooth ((C.pullback q).composite ≫ q ≫ baseStructure p V N hN) := by
    rw [← principalizationHistory_descends, endpointProjection_structure]
    exact paddedPrincipalization_smooth p V N hN
  have : Smooth ((C.pullback q).stageMap (C.pullbackStageIdx q (Fin.last _)) ≫ q ≫ baseStructure p V N hN) := by
    rw [pullbackStageIdx_last]
    change Smooth ((C.pullback q).composite ≫ q ≫ baseStructure p V N hN)
    infer_instance
  have : LocallyOfFinitePresentation (C.stageMap (Fin.last _) ≫ baseStructure p V N hN) := by
    change LocallyOfFinitePresentation (C.composite ≫ baseStructure p V N hN)
    infer_instance
  exact history_stage_smooth_descends C q (endpointSection p V N hN) (endpointSection_projection p V N hN)
    (Fin.last _) (baseStructure p V N hN)

def principalizedOriginalIdeal : (basePrincipalizationHistory p V N hN).last.IdealSheafData :=
  X.singIdeal.comap ((basePrincipalizationHistory p V N hN).composite ≫
    (baseHistory p V N hN).composite ≫ separationProjection X)

theorem principalizedOriginalIdeal_pullback :
    (principalizedOriginalIdeal p V N hN).comap (principalizedProjection p V N hN) =
      (originalIdeal p V N hN).comap (principalizationHistory p V N hN).composite := by
  rw [principalizedOriginalIdeal, originalIdeal, ← comap_comp, ← comap_comp]
  apply congrArg X.singIdeal.comap
  calc
    _ = (principalizedProjection p V N hN ≫ (basePrincipalizationHistory p V N hN).composite) ≫
        (baseHistory p V N hN).composite ≫ separationProjection X := by simp only [Category.assoc]
    _ = (principalizationHistory p V N hN).composite ≫ endpointProjection p V N hN ≫
        (baseHistory p V N hN).composite ≫ separationProjection X := by
      rw [principalizedProjection_over, Category.assoc]
    _ = _ := by rw [← Category.assoc (endpointProjection p V N hN), endpointProjection_over, Category.assoc]

def baseBoundary : Scheme.DivisorFamily (basePrincipalizationHistory p V N hN).last :=
  (basePrincipalizationHistory p V N hN).totalTransformSeq
    (Scheme.DivisorFamily.empty (baseHistory p V N hN).last) (Fin.last _)

private theorem family_comap_comp {A B C : Scheme.{u}} (E : Scheme.DivisorFamily C)
    (f : A ⟶ B) (g : B ⟶ C) : E.comap (f ≫ g) = (E.comap g).comap f := by
  cases E
  simp only [Scheme.DivisorFamily.comap, Scheme.IdealSheafData.comap_comp]

private theorem totalBoundary_transport {B : Scheme.{u}} (S S' : B.BlowUpSequence)
    (E : Scheme.DivisorFamily B) (h : S = S') :
    S.totalTransformSeq E (Fin.last _) = (S'.totalTransformSeq E (Fin.last _)).comap
      (eqToHom (congrArg Scheme.BlowUpSequence.last h)) := by
  subst h
  exact (Scheme.DivisorFamily.comap_id _).symm

theorem baseBoundary_pullback : (baseBoundary p V N hN).comap (principalizedProjection p V N hN) =
    principalizationBoundary (originalTriple p V N hN) := by
  have : Smooth (endpointProjection p V N hN) := endpointProjection_smooth p V N hN
  change ((basePrincipalizationHistory p V N hN).totalTransformSeq
      (Scheme.DivisorFamily.empty (baseHistory p V N hN).last) (Fin.last _)).comap
    (eqToHom (congrArg Scheme.BlowUpSequence.last (principalizationHistory_descends p V N hN)) ≫
      (basePrincipalizationHistory p V N hN).pullbackLastHom (endpointProjection p V N hN)) = _
  rw [family_comap_comp, ← totalBoundary_pullback_last, empty_comap]
  exact (totalBoundary_transport (principalizationHistory p V N hN)
    ((basePrincipalizationHistory p V N hN).pullback (endpointProjection p V N hN))
    (Scheme.DivisorFamily.empty (history p V N hN).last) (principalizationHistory_descends p V N hN)).symm

theorem baseBoundary_snc_pullback : ((baseBoundary p V N hN).comap (principalizedProjection p V N hN)).IsSnc := by
  rw [baseBoundary_pullback]
  exact principalizationBoundary_snc (originalTriple p V N hN)

theorem baseBoundary_original_support : (baseBoundary p V N hN).support = (principalizedOriginalIdeal p V N hN).support := by
  have hu : ((baseBoundary p V N hN).comap (principalizedProjection p V N hN)).support =
      ((principalizedOriginalIdeal p V N hN).comap (principalizedProjection p V N hN)).support := by
    rw [baseBoundary_pullback, principalizedOriginalIdeal_pullback]
    exact principalizationBoundary_original_support (originalTriple p V N hN) (inferInstanceAs (IsEmpty PEmpty))
  have huSet := congrArg (fun Z : Closeds (principalizationHistory p V N hN).last =>
    (Z : Set (principalizationHistory p V N hN).last)) hu
  rw [Hironaka.Resolution.coe_support_comap, support_comap, Closeds.coe_preimage] at huSet
  apply Closeds.ext
  ext x
  have hx := Set.ext_iff.mp huSet (principalizedSection p V N hN x)
  have hp : principalizedProjection p V N hN (principalizedSection p V N hN x) = x :=
    congrArg (fun f => f x) (principalizedSection_projection p V N hN)
  simpa only [Set.mem_preimage, hp] using hx

theorem baseBoundary_isSnc : (baseBoundary p V N hN).IsSnc := by
  let f := (basePrincipalizationHistory p V N hN).composite ≫ baseStructure p V N hN
  have : Smooth f := principalizedBase_smooth p V N hN
  have : Smooth (principalizedProjection p V N hN) := principalizedProjection_smooth p V N hN
  exact ActualSplitSncReflection.isSnc_of_split_pullback (principalizedProjection p V N hN)
    (principalizedSection p V N hN) (principalizedSection_projection p V N hN)
    (fun x => isRegularLocalRing_stalk f x)
    (fun y => isRegularLocalRing_stalk (principalizedProjection p V N hN ≫ f) y)
    (baseBoundary p V N hN) (baseBoundary_snc_pullback p V N hN)

theorem originalSing_inverse_image_isSncDivisor : Scheme.IsSncDivisor
    (((basePrincipalizationHistory p V N hN).composite ≫ (baseHistory p V N hN).composite ≫
      separationProjection X) ⁻¹' X.singularLocus) := by
  refine ⟨baseBoundary p V N hN, baseBoundary_isSnc p V N hN, ?_⟩
  rw [baseBoundary_original_support, principalizedOriginalIdeal, support_comap, Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus p]

end
end Hironaka.Resolution.Algebraic.ActualGlobalPrincipalizedEndpoint
