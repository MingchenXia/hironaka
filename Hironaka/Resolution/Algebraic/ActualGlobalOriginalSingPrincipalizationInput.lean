import Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingNonzero

/-!
# ONE ORIGINAL-singular principalization on the SAME global padded endpoint

Source-first proof: `actual-global-original-sing-principalization-input-20261102.tex`.
Actual final split geometry and local Cartier nonzero produce the true input.
The SAME uniform input dimension extends through the dense ORIGINAL regular open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData Scheme.BlowUpSequence Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingPrincipalizationInput

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingNonzero ActualPaddedNativePrincipalizationInput

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

private instance inputStructure_finitePresentation : LocallyOfFinitePresentation (envelopeStructure p V) :=
  inferInstance

private instance history_compositeProper : IsProper (history p V N hN).composite := by
  have : IsLocallyNoetherian (envelope X V) :=
    LocallyOfFiniteType.isLocallyNoetherian (envelopeStructure p V)
  exact (history p V N hN).isProper_composite

/-- Actual final projection of the SAME entire global history, with no clock adjustment. -/
def endpointProjection : (history p V N hN).last ⟶ (baseHistory p V N hN).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (history_descends p V N hN)) ≫
    (baseHistory p V N hN).pullbackLastHom (projection X V)

theorem endpoint_isPullback : IsPullback (endpointProjection p V N hN) (history p V N hN).composite
    (baseHistory p V N hN).composite (projection X V) := by
  have : Smooth (projection X V) := projection_smooth X V
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq (baseHistory p V N hN)
    (projection X V) (history p V N hN) (history_descends p V N hN)

theorem endpointProjection_over : endpointProjection p V N hN ≫ (baseHistory p V N hN).composite =
    (history p V N hN).composite ≫ projection X V := (endpoint_isPullback p V N hN).w

theorem endpointProjection_smooth : Smooth (endpointProjection p V N hN) :=
  property_of_isPullback _ (endpoint_isPullback p V N hN) (projection_smooth X V)

theorem endpointProjection_affine : IsAffineHom (endpointProjection p V N hN) :=
  property_of_isPullback _ (endpoint_isPullback p V N hN) (projection_affine X V)

theorem endpointProjection_surjective : Surjective (endpointProjection p V N hN) := by
  exact property_of_isPullback _ (endpoint_isPullback p V N hN) (projection_surjective X V)

/-- The OWN final section constructed from the actual cartesian universal property. -/
def endpointSection : (baseHistory p V N hN).last ⟶ (history p V N hN).last :=
  (endpoint_isPullback p V N hN).lift (𝟙 _) ((baseHistory p V N hN).composite ≫ zeroSection X V)
    (by simp [zeroSection_projection])

theorem endpointSection_projection : endpointSection p V N hN ≫ endpointProjection p V N hN =
    𝟙 (baseHistory p V N hN).last := (endpoint_isPullback p V N hN).lift_fst _ _ _

theorem endpointSection_original : endpointSection p V N hN ≫ (history p V N hN).composite =
    (baseHistory p V N hN).composite ≫ zeroSection X V := (endpoint_isPullback p V N hN).lift_snd _ _ _

def endpointStructure : (history p V N hN).last ⟶ Spec (.of k) :=
  (history p V N hN).composite ≫ envelopeStructure p V

instance endpointStructure_finiteType : FiniteType (endpointStructure p V N hN) := by
  dsimp only [endpointStructure]
  infer_instance

instance endpointStructure_separated : IsSeparated (endpointStructure p V N hN) := by
  dsimp only [endpointStructure]
  infer_instance

instance endpointStructure_smooth : Smooth (endpointStructure p V N hN) :=
  (history_isStrongResolution p V N hN).smooth

/-- The actual ORIGINAL global singular ideal, on the SAME padded native endpoint. -/
def originalIdeal : (history p V N hN).last.IdealSheafData :=
  X.singIdeal.comap ((history p V N hN).composite ≫ projection X V ≫
    ActualGlobalDimensionClopenPartition.separationProjection X)

theorem originalIdeal_nonzero : (originalIdeal p V N hN).IsNonzeroEverywhere := by
  have : Smooth (endpointProjection p V N hN) := endpointProjection_smooth p V N hN
  have hnz := isNonzeroEverywhere_comap_of_flat (endpointProjection p V N hN)
    (baseOriginalIdeal_nonzero p V N hN)
  have heq : originalIdeal p V N hN = (baseOriginalIdeal p V N hN).comap (endpointProjection p V N hN) := by
    rw [originalIdeal, baseOriginalIdeal, ← comap_comp]
    apply congrArg X.singIdeal.comap
    simpa only [Category.assoc] using congrArg
      (fun f => f ≫ ActualGlobalDimensionClopenPartition.separationProjection X)
      (endpointProjection_over p V N hN).symm
  exact heq.symm ▸ hnz

theorem originalIdeal_support : ((originalIdeal p V N hN).support : Set (history p V N hN).last) =
    ((history p V N hN).composite ≫ projection X V ≫
      ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹' X.singularLocus := by
  rw [originalIdeal, support_comap, Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus p]

def originalRegularOpen : (history p V N hN).last.Opens :=
  ((history p V N hN).composite ≫ projection X V ≫
    ActualGlobalDimensionClopenPartition.separationProjection X) ⁻¹ᵁ p.smoothLocus

theorem originalRegularOpen_dense : Dense (originalRegularOpen p V N hN : Set (history p V N hN).last) := by
  have : IsReduced (history p V N hN).last :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (endpointStructure p V N hN)
  have hd := dense_compl_support_of_nonzero (originalIdeal p V N hN) (originalIdeal_nonzero p V N hN)
  have hs : ((originalIdeal p V N hN).support : Set (history p V N hN).last) =
      (originalRegularOpen p V N hN : Set (history p V N hN).last)ᶜ := by
    rw [originalIdeal_support, Scheme.singularLocus_eq_compl_smoothLocus p]
    rfl
  rw [hs, compl_compl] at hd
  exact hd

/-- ONE SAME original input dimension extends over the ENTIRE SAME smooth padded endpoint. -/
theorem endpoint_same_dimension : ∃ n : ℕ,
    SmoothOfRelativeDimension n ((envelopeStructure p V).smoothLocus.ι ≫ envelopeStructure p V) ∧
      SmoothOfRelativeDimension n (endpointStructure p V N hN) := by
  obtain ⟨n, hn⟩ := (variableEnvelope p V N hN).property.2
  have : SmoothOfRelativeDimension n ((envelopeStructure p V).smoothLocus.ι ≫ envelopeStructure p V) := hn
  refine ⟨n, hn, ?_⟩
  let W := originalRegularOpen p V N hN
  have hle : W ≤ (history p V N hN).composite ⁻¹ᵁ (envelopeStructure p V).smoothLocus :=
    fun _ hx => ActualGlobalOriginalRegularGeometry.paddedOriginalRegular_le_smoothLocus p V N hN hx
  have : IsIso ((history p V N hN).composite ∣_ (envelopeStructure p V).smoothLocus) :=
    (history_isStrongResolution p V N hN).isIso_restrict_smoothLocus
  have : IsOpenImmersion ((history p V N hN).composite.resLE
      (envelopeStructure p V).smoothLocus W hle) := by
    dsimp only [Scheme.Hom.resLE]
    infer_instance
  have : SmoothOfRelativeDimension (0 + n) ((history p V N hN).composite.resLE
      (envelopeStructure p V).smoothLocus W hle ≫
        ((envelopeStructure p V).smoothLocus.ι ≫ envelopeStructure p V)) := inferInstance
  rw [Nat.zero_add, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc] at this
  have : SmoothOfRelativeDimension n (W.ι ≫ endpointStructure p V N hN) := this
  exact relativeDimension_of_dense_open (endpointStructure p V N hN) W
    (originalRegularOpen_dense p V N hN) n

/-- Actual valid triple with the true ORIGINAL ideal on this ONE native padded endpoint. -/
def originalTriple : Triple k where
  X := .ofHom (endpointStructure p V N hN) inferInstance inferInstance
  smoothOfRelativeDimension := by
    obtain ⟨n, -, hn⟩ := endpoint_same_dimension p V N hN
    exact ⟨n, hn⟩
  I := originalIdeal p V N hN
  isNonzeroEverywhere := originalIdeal_nonzero p V N hN
  E := Scheme.DivisorFamily.empty _
  isSnc := isSnc_empty_of_smooth (endpointStructure p V N hN)

/-- ONE actual native original-singular principalization, with its entire native clock. -/
def principalizationHistory : (history p V N hN).last.BlowUpSequence := BP (originalTriple p V N hN)

theorem principalizationHistory_isSNC :
    ((originalIdeal p V N hN).comap (principalizationHistory p V N hN).composite).IsIdealOfSncDivisor :=
  BP_isIdealOfSncDivisor (originalTriple p V N hN)

end
end Hironaka.Resolution.Algebraic.ActualGlobalOriginalSingPrincipalizationInput
