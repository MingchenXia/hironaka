import Hironaka.Resolution.Algebraic.ActualGlobalPaddedCompleteSmoothComparison

/-!
# SAME global ORIGINAL strong-resolution histories and both smooth clauses

Source-first proof: `actual-global-strong-resolution-smooth-naturality-20261102.tex`.
Actual whole chronological padded descent, flat-SURJ cancellation and real
original-centre transport derive smooth compatibility of one final assignment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothNaturality

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity ActualGlobalDimensionClopenPartition
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingPrincipalizationInput ActualGlobalOriginalSingPrincipalizationHistoryDescent
  ActualGlobalSeparationBlowupFunctoriality ActualGlobalPaddedSmoothComparison
  ActualGlobalStrongResolutionSmoothSurjective ActualGlobalMixedDimensionResolution

theorem cons_eraseEmpty_eq_pullback_of_ideal_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (S : I.blowUp.BlowUpSequence)
    (T : J.blowUp.BlowUpSequence) (hJ : I.comap f = J)
    (hT : T = (S.pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp hJ.symm) ≫
      Scheme.Hom.blowUpMap f I)).eraseEmpty) :
    (Scheme.BlowUpSequence.cons Y J T).eraseEmpty =
      ((Scheme.BlowUpSequence.cons X I S).pullback f).eraseEmpty := by
  subst J
  simp only [eqToHom_refl, Category.id_comp] at hT
  rw [pullback_cons, hT]
  exact eraseEmpty_cons_eraseEmpty _ _

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]

def canonicalBaseCompleteHistory : (separationSpace X).BlowUpSequence :=
  (canonicalBaseHistory p).concat (basePrincipalizationHistory p (paddingVariables p) (commonDimension p) (padding_rank p))

theorem baseCompleteHistory_eq_canonical (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    (baseHistory p V N hN).concat (basePrincipalizationHistory p V N hN) = canonicalBaseCompleteHistory p := by
  have h := ActualGlobalPaddingPrincipalizationChoice.originalHistory_eq_canonical p V N hN
  change Scheme.BlowUpSequence.cons X (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
      ((baseHistory p V N hN).concat (basePrincipalizationHistory p V N hN)) =
    Scheme.BlowUpSequence.cons X (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
      (canonicalBaseCompleteHistory p) at h
  exact eq_of_heq (Scheme.BlowUpSequence.cons.inj h).2

theorem paddedCompleteHistory_descends (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    (history p V N hN).concat (principalizationHistory p V N hN) =
      (canonicalBaseCompleteHistory p).pullback (projection X V) := by
  have h := concat_eq_pullback_of_eq (projection X V) (baseHistory p V N hN) (history p V N hN)
    (basePrincipalizationHistory p V N hN) (principalizationHistory p V N hN)
    (history_descends p V N hN) (principalizationHistory_descends p V N hN)
  rw [baseCompleteHistory_eq_canonical] at h
  exact h

variable {Y : Scheme.{u}} [IsNoetherian Y] [IsReduced Y]
    (f : Y ⟶ X) [Smooth f] [IsSeparated (f ≫ p)]

theorem canonicalBaseCompleteHistory_smooth_eraseEmpty : canonicalBaseCompleteHistory (f ≫ p) =
    ((canonicalBaseCompleteHistory p).pullback (separationMap p f)).eraseEmpty := by
  let q := projection Y (sourceVariables p f)
  have : Smooth q := projection_smooth Y (sourceVariables p f)
  have hq : Function.Surjective q := (projection_surjective Y (sourceVariables p f)).1
  apply pullback_injective_of_surjective q hq
  calc
    (canonicalBaseCompleteHistory (f ≫ p)).pullback q =
        (history (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)).concat
          (principalizationHistory (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)) :=
      (paddedCompleteHistory_descends (f ≫ p) (sourceVariables p f) (sourceDimension p f) (source_rank p f)).symm
    _ = (((canonicalHistory p).concat (principalizationHistory p (paddingVariables p)
        (commonDimension p) (padding_rank p))).pullback (comparisonMap p f)).eraseEmpty :=
      ActualGlobalPaddedCompleteSmoothComparison.paddedCompleteHistory_eq_eraseEmpty_pullback p f
    _ = (((canonicalBaseCompleteHistory p).pullback (projection X (paddingVariables p))).pullback
        (comparisonMap p f)).eraseEmpty := by
      rw [paddedCompleteHistory_descends p (paddingVariables p) (commonDimension p) (padding_rank p)]
    _ = (((canonicalBaseCompleteHistory p).pullback (separationMap p f)).pullback q).eraseEmpty := by
      rw [← pullback_comp, ← pullback_comp, comparisonMap_projection]
    _ = (((canonicalBaseCompleteHistory p).pullback (separationMap p f)).eraseEmpty).pullback q :=
      eraseEmpty_pullback_of_flat_surjective _ q hq

theorem canonicalOriginalHistory_smooth_eraseEmpty : (canonicalOriginalHistory (f ≫ p)).eraseEmpty =
    ((canonicalOriginalHistory p).pullback f).eraseEmpty :=
  cons_eraseEmpty_eq_pullback_of_ideal_eq f (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
    (ActualGlobalDimensionSeparationIdeal.separationIdeal Y) (canonicalBaseCompleteHistory p)
    (canonicalBaseCompleteHistory (f ≫ p)) (ActualGlobalSeparationSmoothNaturality.separationIdeal_smooth p f)
    (canonicalBaseCompleteHistory_smooth_eraseEmpty p f)

def resolutionHistory : X.BlowUpSequence := (canonicalOriginalHistory p).eraseEmpty

theorem resolutionHistory_smooth_surjective [Surjective f] :
    resolutionHistory (f ≫ p) = (resolutionHistory p).pullback f := by
  change (canonicalOriginalHistory (f ≫ p)).eraseEmpty = (canonicalOriginalHistory p).eraseEmpty.pullback f
  rw [canonicalOriginalHistory_smooth_surjective p f,
    eraseEmpty_pullback_of_flat_surjective _ f (inferInstance : Surjective f).1]

theorem resolutionHistory_smooth : resolutionHistory (f ≫ p) = ((resolutionHistory p).pullback f).eraseEmpty := by
  change (canonicalOriginalHistory (f ≫ p)).eraseEmpty = ((canonicalOriginalHistory p).eraseEmpty.pullback f).eraseEmpty
  rw [eraseEmpty_pullback_eraseEmpty']
  exact canonicalOriginalHistory_smooth_eraseEmpty p f

omit f in
theorem resolutionHistory_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (originalAlgScheme p) (resolutionHistory p) := by
  let S := canonicalOriginalHistory p
  have hs := canonicalOriginalHistory_isStrongResolution p
  have : Smooth (S.composite ≫ p) := hs.smooth
  have : IsIso (S.composite ∣_ p.smoothLocus) := hs.isIso_restrict_smoothLocus
  have hsm : Smooth (S.eraseEmpty.composite ≫ p) := by
    rw [← eraseEmptyLastHom_comp_composite S, Category.assoc]
    infer_instance
  have hreg : IsIso (S.eraseEmpty.composite ∣_ p.smoothLocus) := isIso_eraseEmpty_composite_restrict S _
  refine ⟨⟨hsm, (resolutionHistory p).isProjective_composite,
    p.smoothLocus, p.dense_smoothLocus_of_perfectField, hreg⟩, hreg, ?_⟩
  obtain ⟨D, hD, hsupp⟩ := hs.isSncDivisor_preimage
  refine ⟨D.comap S.eraseEmptyLastHom, isSnc_comap_of_smooth (S.composite ≫ p) S.eraseEmptyLastHom hD, ?_⟩
  rw [Hironaka.Resolution.coe_support_comap, hsupp]
  change (S.eraseEmptyLastHom ≫ S.composite) ⁻¹' (p.smoothLocus : Set X)ᶜ =
    S.eraseEmpty.composite ⁻¹' (p.smoothLocus : Set X)ᶜ
  rw [eraseEmptyLastHom_comp_composite S]

end
end Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothNaturality
