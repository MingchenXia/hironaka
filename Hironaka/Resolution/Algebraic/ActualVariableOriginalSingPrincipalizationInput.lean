import Hironaka.Resolution.Algebraic.ActualVariablePaddingNativeHistory

/-!
# Genuine ORIGINAL-singular BP inputs on every SAME actual padded native endpoint

Source-first proof: `actual-variable-original-sing-principalization-input-20261102.tex`.
Actual flat terminal geometry derives the genuine ORIGINAL ideal nonzero;
the dense inverse ORIGINAL regular locus derives entire endpoint purity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData Scheme.BlowUpSequence Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualVariableOriginalSingPrincipalizationInput

noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupRegularLocus ActualDimensionGroupEquidimensionalPieces
  ActualDimensionGroupPaddedCover ActualRelativeAffineHistoryDescent ActualOriginalSingIdealNonzero
  ActualPaddedNativePrincipalizationInput ActualCommonNativeResolutionComparison ActualVariablePaddingNativeHistory

variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]
  (V : dimensionIndex R → Type u) [∀ d, Finite (V d)]
  (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)

private abbrev originalStructure : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

private instance originalStructure_finiteType : LocallyOfFiniteType (originalStructure R k) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

private abbrev inputStructure : ActualVariablePaddingEnvelope.envelope R V ⟶ Spec (.of k) :=
  (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN).obj.hom

private instance inputStructure_finiteType : FiniteType (inputStructure R k V N hN) :=
  (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN).obj.prop.1

private instance inputStructure_separated : IsSeparated (inputStructure R k V N hN) :=
  (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN).obj.prop.2

private instance inputStructure_finitePresentation : LocallyOfFinitePresentation (inputStructure R k V N hN) :=
  inferInstance

private instance history_compositeProper : IsProper (history R k V N hN).composite := by
  have : IsLocallyNoetherian (ActualVariablePaddingEnvelope.envelope R V) :=
    LocallyOfFiniteType.isLocallyNoetherian (inputStructure R k V N hN)
  exact (history R k V N hN).isProper_composite

private abbrev endpointStructure : (history R k V N hN).last ⟶ Spec (.of k) :=
  (history R k V N hN).composite ≫ inputStructure R k V N hN

private instance endpointStructure_finiteType : FiniteType (endpointStructure R k V N hN) := by
  dsimp only [endpointStructure]
  infer_instance

private instance endpointStructure_separated : IsSeparated (endpointStructure R k V N hN) := by
  dsimp only [endpointStructure]
  infer_instance

private instance endpointStructure_smooth : Smooth (endpointStructure R k V N hN) :=
  (history_isStrongResolution R k V N hN).smooth

/-- The genuine ORIGINAL singular ideal on the SAME arbitrary-padding native endpoint. -/
def originalIdeal : (history R k V N hN).last.IdealSheafData :=
  (Spec (.of R)).singIdeal.comap ((history R k V N hN).composite ≫
    ActualVariablePaddingEnvelope.projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R))

/-- Actual flat terminal geometry proves genuine ORIGINAL-ideal nonzero, not a supplied certificate. -/
theorem originalIdeal_nonzero : (originalIdeal R k V N hN).IsNonzeroEverywhere := by
  have : Smooth (endpointProjection R k V N hN) := endpointProjection_smooth R k V N hN
  have hnz := isNonzeroEverywhere_comap_of_flat (endpointProjection R k V N hN)
    (originalSingPullback_nonzero R k)
  have heq : originalIdeal R k V N hN = (originalSingPullback R k).comap (endpointProjection R k V N hN) := by
    rw [originalIdeal,originalSingPullback,← comap_comp]
    apply congrArg (Spec (.of R)).singIdeal.comap
    simpa only [Category.assoc] using congrArg (fun f => f ≫ affineBlowUp.π (dimensionSeparationIdeal R))
      (endpointProjection_over R k V N hN).symm
  exact heq.symm ▸ hnz

/-- The actual ORIGINAL support is exactly the inverse ORIGINAL singular locus. -/
theorem originalIdeal_support : ((originalIdeal R k V N hN).support : Set (history R k V N hN).last) =
    ((history R k V N hN).composite ≫ ActualVariablePaddingEnvelope.projection R V ≫
      affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹' (Spec (.of R)).singularLocus := by
  rw [originalIdeal,support_comap,Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus (originalStructure R k)]

/-- The inverse ENTIRE ORIGINAL regular open on the SAME native endpoint. -/
def originalRegularOpen : (history R k V N hN).last.Opens :=
  ((history R k V N hN).composite ≫ ActualVariablePaddingEnvelope.projection R V ≫
    affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ (originalStructure R k).smoothLocus

/-- Actual nonvanishing on the reduced native endpoint proves density of the ORIGINAL regular inverse image. -/
theorem originalRegularOpen_dense : Dense (originalRegularOpen R k V N hN : Set (history R k V N hN).last) := by
  have : IsReduced (history R k V N hN).last :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (endpointStructure R k V N hN)
  have hd := dense_compl_support_of_nonzero (originalIdeal R k V N hN) (originalIdeal_nonzero R k V N hN)
  have hs : ((originalIdeal R k V N hN).support : Set (history R k V N hN).last) =
      (originalRegularOpen R k V N hN : Set (history R k V N hN).last)ᶜ := by
    rw [originalIdeal_support,Scheme.singularLocus_eq_compl_smoothLocus (originalStructure R k)]
    rfl
  rw [hs,compl_compl] at hd
  exact hd

private theorem originalRegular_le_input_smoothLocus :
    (ActualVariablePaddingEnvelope.projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ
      (originalStructure R k).smoothLocus ≤ (inputStructure R k V N hN).smoothLocus := by
  let U := (originalStructure R k).smoothLocus
  let g := ActualVariablePaddingEnvelope.projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R)
  let W := g ⁻¹ᵁ U
  have : Smooth (ActualVariablePaddingEnvelope.projection R V) := ActualVariablePaddingEnvelope.projection_smooth R V
  have : IsIso (affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U) := separation_isIso_over_smoothLocus R k
  have : Smooth (U.ι ≫ originalStructure R k) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,← Scheme.Hom.preimage_smoothLocus_eq]
    exact U.ι_preimage_self
  have hcomp : Smooth (g ∣_ U ≫ U.ι ≫ originalStructure R k) := by
    rw [show g ∣_ U = ActualVariablePaddingEnvelope.projection R V ∣_
        (affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ U ≫ affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U
      from morphismRestrict_comp _ _ _]
    infer_instance
  have : Smooth (W.ι ≫ inputStructure R k V N hN) := by
    have he : g ∣_ U ≫ U.ι ≫ originalStructure R k = W.ι ≫ inputStructure R k V N hN := by
      rw [← Category.assoc,morphismRestrict_ι]
      rfl
    exact he ▸ hcomp
  exact fun x hx => ((inputStructure R k V N hN).mem_smoothLocus_iff_exists_smooth).mpr ⟨W,hx,inferInstance⟩

/-- ONE SAME input uniform dimension extends through the dense ORIGINAL regular open to the ENTIRE smooth endpoint. -/
theorem endpoint_same_dimension : ∃ n : ℕ,
    SmoothOfRelativeDimension n ((inputStructure R k V N hN).smoothLocus.ι ≫ inputStructure R k V N hN) ∧
      SmoothOfRelativeDimension n (endpointStructure R k V N hN) := by
  obtain ⟨n,hn⟩ := (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN).property.2
  have : SmoothOfRelativeDimension n ((inputStructure R k V N hN).smoothLocus.ι ≫ inputStructure R k V N hN) := hn
  refine ⟨n,hn,?_⟩
  let W := originalRegularOpen R k V N hN
  have hle : W ≤ (history R k V N hN).composite ⁻¹ᵁ (inputStructure R k V N hN).smoothLocus :=
    fun _ hx => originalRegular_le_input_smoothLocus R k V N hN hx
  have : IsIso ((history R k V N hN).composite ∣_ (inputStructure R k V N hN).smoothLocus) :=
    (history_isStrongResolution R k V N hN).isIso_restrict_smoothLocus
  have : IsOpenImmersion ((history R k V N hN).composite.resLE
      (inputStructure R k V N hN).smoothLocus W hle) := by
    dsimp only [Scheme.Hom.resLE]
    infer_instance
  have : SmoothOfRelativeDimension (0 + n) ((history R k V N hN).composite.resLE
      (inputStructure R k V N hN).smoothLocus W hle ≫
        ((inputStructure R k V N hN).smoothLocus.ι ≫ inputStructure R k V N hN)) := inferInstance
  rw [Nat.zero_add,← Category.assoc,Scheme.Hom.resLE_comp_ι,Category.assoc] at this
  have : SmoothOfRelativeDimension n (W.ι ≫ endpointStructure R k V N hN) := this
  exact relativeDimension_of_dense_open (endpointStructure R k V N hN) W
    (originalRegularOpen_dense R k V N hN) n

/-- Actual valid native ORIGINAL-singular triple on the SAME arbitrary-padding native smooth endpoint. -/
def originalTriple : Triple k where
  X := .ofHom (endpointStructure R k V N hN) inferInstance inferInstance
  smoothOfRelativeDimension := by
    obtain ⟨n,-,hn⟩ := endpoint_same_dimension R k V N hN
    exact ⟨n,hn⟩
  I := originalIdeal R k V N hN
  isNonzeroEverywhere := originalIdeal_nonzero R k V N hN
  E := Scheme.DivisorFamily.empty _
  isSnc := isSnc_empty_of_smooth (endpointStructure R k V N hN)

/-- ONE deterministic native BP on the SAME genuine original-singular triple. -/
def principalizationHistory : (history R k V N hN).last.BlowUpSequence := BP (originalTriple R k V N hN)

/-- The actual ORIGINAL ideal has native SNC pullback through this ONE BP. -/
theorem principalizationHistory_isSNC :
    ((originalIdeal R k V N hN).comap (principalizationHistory R k V N hN).composite).IsIdealOfSncDivisor :=
  BP_isIdealOfSncDivisor (originalTriple R k V N hN)

/-- Canonical padding gives EXACTLY the original genuine native triple. -/
theorem canonicalTriple :
    originalTriple R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k) =
      nativeOriginalSingPrincipalizationTriple R k := by
  rfl

/-- Canonical padding gives EXACTLY the SAME original ONE native BP, with its entire original clock. -/
theorem canonicalPrincipalization :
    principalizationHistory R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k) =
      nativeOriginalSingPrincipalizationHistory R k := by
  rfl

end
end Hironaka.Resolution.Algebraic.ActualVariableOriginalSingPrincipalizationInput
