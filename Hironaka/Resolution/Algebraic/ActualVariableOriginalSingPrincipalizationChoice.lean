import Hironaka.Resolution.Algebraic.ActualVariableOriginalSingPrincipalizationInput

/-!
# Genuine ORIGINAL-singular BP and whole original history are independent of padding

Source-first proof: `actual-variable-original-sing-principalization-choice-20261102.tex`.
Actual complete-blowup uniqueness and actual cartesian lifts compare the ONE
common native BP clock through ONE genuinely constructed common section.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualVariableOriginalSingPrincipalizationChoice

noncomputable section

/-- Real complete-blowup universality gives uniqueness over the actual original composite for a flat source. -/
theorem composite_hom_ext_of_flat {X Y : Scheme.{u}} [IsNoetherian X] (S : X.BlowUpSequence)
    (f g : Y ⟶ S.last) [Flat g] (h : f ≫ S.composite = g ≫ S.composite) : f = g := by
  obtain ⟨K,-,e,he,-⟩ := exists_blowUp_composite_iso S
  have hK : (K.comap S.composite).IsInvertible := by
    rw [← he,comap_comp]
    exact IsInvertible.comap_of_isOpenImmersion e.hom (blowUp.isBlowUp K).admissible
  have hKg : (K.comap (g ≫ S.composite)).IsInvertible := by
    rw [comap_comp]
    exact IsInvertible.comap_of_flat g hK
  apply (cancel_mono e.hom).mp
  exact (blowUp.isBlowUp K).hom_ext (g ≫ S.composite) hKg (f ≫ e.hom) (g ≫ e.hom)
    (by rw [Category.assoc,he,h]) (by rw [Category.assoc,he])

open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces ActualDimensionGroupPaddedCover
  ActualRelativeAffineHistoryDescent ActualCommonNativeResolutionComparison ActualVariablePaddingNativeHistory
  ActualVariableOriginalSingPrincipalizationInput ActualPaddedEnvelopeNativeTranslations

private theorem base_noetherian (R : Type u) [CommRing R] (k : Type u) [Field k]
    [Algebra k R] [Algebra.FiniteType k R] : IsNoetherian (affineBlowUp (dimensionSeparationIdeal R)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let f : affineBlowUp (dimensionSeparationIdeal R) ⟶ Spec (.of k) :=
    affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  have : LocallyOfFiniteType f := by dsimp only [f]; infer_instance
  have : QuasiCompact f := by dsimp only [f]; infer_instance
  exact f.isNoetherian_of_field

variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- Real final cartesian lift of ANY actual original input section. -/
def sectionFor (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)
    (s : affineBlowUp (dimensionSeparationIdeal R) ⟶ ActualVariablePaddingEnvelope.envelope R V)
    (hs : s ≫ ActualVariablePaddingEnvelope.projection R V = 𝟙 _) :
    (nativeBaseHistory R k).last ⟶ (history R k V N hN).last :=
  (endpoint_isPullback R k V N hN).lift (𝟙 _) ((nativeBaseHistory R k).composite ≫ s) (by simp [hs])

/-- Actual final retraction for the genuine cartesian lift. -/
theorem sectionFor_projection (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)
    (s : affineBlowUp (dimensionSeparationIdeal R) ⟶ ActualVariablePaddingEnvelope.envelope R V)
    (hs : s ≫ ActualVariablePaddingEnvelope.projection R V = 𝟙 _) :
    sectionFor R k V N hN s hs ≫ endpointProjection R k V N hN = 𝟙 _ :=
  (endpoint_isPullback R k V N hN).lift_fst _ _ _

/-- Genuine original-input equation for the same actual final lift. -/
theorem sectionFor_original (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)
    (s : affineBlowUp (dimensionSeparationIdeal R) ⟶ ActualVariablePaddingEnvelope.envelope R V)
    (hs : s ≫ ActualVariablePaddingEnvelope.projection R V = 𝟙 _) :
    sectionFor R k V N hN s hs ≫ (history R k V N hN).composite = (nativeBaseHistory R k).composite ≫ s :=
  (endpoint_isPullback R k V N hN).lift_snd _ _ _

/-- The actual base BP through its genuine final original-zero section. -/
def basePrincipalizationHistory (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) : (nativeBaseHistory R k).last.BlowUpSequence :=
  (principalizationHistory R k V N hN).pullback (endpointSection R k V N hN)

section ActualMap
variable (V₀ V₁ : dimensionIndex R → Type u) [∀ d, Finite (V₀ d)] [∀ d, Finite (V₁ d)]
  (N₀ N₁ : ℕ) (h₀ : ∀ d, dimensionNat R k d + Nat.card (V₀ d) = N₀)
  (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
  (g : ActualVariablePaddingEnvelope.envelope R V₀ ⟶ ActualVariablePaddingEnvelope.envelope R V₁)
  [Smooth g] [Surjective g]
  (hg : g ≫ ActualVariablePaddingEnvelope.projection R V₁ = ActualVariablePaddingEnvelope.projection R V₀)

private def inputMap : ActualVariablePaddingEnvelope.variableEnvelope R V₀ k N₀ h₀ ⟶
    ActualVariablePaddingEnvelope.variableEnvelope R V₁ k N₁ h₁ :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk g (by
    change g ≫ (ActualVariablePaddingEnvelope.projection R V₁ ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
    rw [← Category.assoc,hg]
    rfl))

include hg in
private theorem resolutionEq : history R k V₀ N₀ h₀ = (history R k V₁ N₁ h₁).pullback g := by
  let f := inputMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg
  have hs : Smooth (HasUnderlyingScheme.hom f) := by
    change Smooth g
    infer_instance
  have hsurj : Function.Surjective (HasUnderlyingScheme.hom f) := by
    change Function.Surjective g
    exact (inferInstance : Surjective g).1
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective f hs hsurj

def nativeEndpointMap : (history R k V₀ N₀ h₀).last ⟶ (history R k V₁ N₁ h₁).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (resolutionEq R k V₀ V₁ N₀ N₁ h₀ h₁ g hg)) ≫
    (history R k V₁ N₁ h₁).pullbackLastHom g

private theorem endpointMap_square : IsPullback (nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg)
    (history R k V₀ N₀ h₀).composite (history R k V₁ N₁ h₁).composite g :=
  ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq (history R k V₁ N₁ h₁) g
    (history R k V₀ N₀ h₀) (resolutionEq R k V₀ V₁ N₀ N₁ h₀ h₁ g hg)

private theorem endpointMap_over : nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg ≫ (history R k V₁ N₁ h₁).composite =
    (history R k V₀ N₀ h₀).composite ≫ g := (endpointMap_square R k V₀ V₁ N₀ N₁ h₀ h₁ g hg).w

private theorem endpointMap_smooth : Smooth (nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg) :=
  property_of_isPullback _ (endpointMap_square R k V₀ V₁ N₀ N₁ h₀ h₁ g hg) (inferInstance : Smooth g)

private theorem endpointMap_surjective : Surjective (nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg) :=
  property_of_isPullback _ (endpointMap_square R k V₀ V₁ N₀ N₁ h₀ h₁ g hg) (inferInstance : Surjective g)

private theorem endpointMap_projection : nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg ≫ endpointProjection R k V₁ N₁ h₁ =
    endpointProjection R k V₀ N₀ h₀ := by
  have : IsNoetherian (affineBlowUp (dimensionSeparationIdeal R)) := base_noetherian R k
  have : Smooth (endpointProjection R k V₀ N₀ h₀) := endpointProjection_smooth R k V₀ N₀ h₀
  apply composite_hom_ext_of_flat (nativeBaseHistory R k)
  calc
    _ = nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg ≫
        ((history R k V₁ N₁ h₁).composite ≫ ActualVariablePaddingEnvelope.projection R V₁) := by
      rw [Category.assoc,endpointProjection_over]
    _ = ((history R k V₀ N₀ h₀).composite ≫ g) ≫ ActualVariablePaddingEnvelope.projection R V₁ := by
      rw [← Category.assoc,endpointMap_over]
    _ = (history R k V₀ N₀ h₀).composite ≫ ActualVariablePaddingEnvelope.projection R V₀ := by
      rw [Category.assoc,hg]
    _ = endpointProjection R k V₀ N₀ h₀ ≫ (nativeBaseHistory R k).composite :=
      (endpointProjection_over R k V₀ N₀ h₀).symm

theorem principalization_eq_pullback : principalizationHistory R k V₀ N₀ h₀ =
    (principalizationHistory R k V₁ N₁ h₁).pullback (nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg) := by
  let m := nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg
  let T₀ := originalTriple R k V₀ N₀ h₀
  let T₁ := originalTriple R k V₁ N₁ h₁
  have : Smooth m := endpointMap_smooth R k V₀ V₁ N₀ N₁ h₀ h₁ g hg
  have he : m ≫ ((history R k V₁ N₁ h₁).composite ≫ ActualVariablePaddingEnvelope.projection R V₁) =
      (history R k V₀ N₀ h₀).composite ≫ ActualVariablePaddingEnvelope.projection R V₀ := by
    rw [← Category.assoc,endpointMap_over,Category.assoc,hg]
  have hf : m ≫ (T₁.X.left ↘ Spec (.of k)) = T₀.X.left ↘ Spec (.of k) := by
    change m ≫ ((history R k V₁ N₁ h₁).composite ≫ ActualVariablePaddingEnvelope.projection R V₁ ≫
      affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) =
        (history R k V₀ N₀ h₀).composite ≫ ActualVariablePaddingEnvelope.projection R V₀ ≫
          affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
    simpa only [Category.assoc] using congrArg (fun f => f ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) he
  have hI : T₀.I = T₁.I.comap m := by
    change originalIdeal R k V₀ N₀ h₀ = (originalIdeal R k V₁ N₁ h₁).comap m
    rw [originalIdeal,originalIdeal,← comap_comp]
    apply congrArg (Spec (.of R)).singIdeal.comap
    simpa only [Category.assoc] using (congrArg (fun f => f ≫ affineBlowUp.π (dimensionSeparationIdeal R)) he).symm
  have hE : T₀.E = T₁.E.comap m := (empty_comap m).symm
  exact BP_pullback_of_surjective T₁ T₀ m (endpointMap_surjective R k V₀ V₁ N₀ N₁ h₀ h₁ g hg).1 ⟨hf,hI,hE⟩

private theorem section_compatibility
    (s : affineBlowUp (dimensionSeparationIdeal R) ⟶ ActualVariablePaddingEnvelope.envelope R V₀)
    (hs : s ≫ ActualVariablePaddingEnvelope.projection R V₀ = 𝟙 _)
    (hsg : s ≫ g = ActualVariablePaddingEnvelope.zeroSection R V₁) :
    sectionFor R k V₀ N₀ h₀ s hs ≫ nativeEndpointMap R k V₀ V₁ N₀ N₁ h₀ h₁ g hg = endpointSection R k V₁ N₁ h₁ := by
  apply (endpoint_isPullback R k V₁ N₁ h₁).hom_ext
  · rw [Category.assoc,endpointMap_projection,sectionFor_projection,endpointSection_projection]
  · rw [Category.assoc,endpointMap_over,← Category.assoc,sectionFor_original,Category.assoc,hsg,
      endpointSection_original]

include hg in
private theorem principalization_section_eq
    (s : affineBlowUp (dimensionSeparationIdeal R) ⟶ ActualVariablePaddingEnvelope.envelope R V₀)
    (hs : s ≫ ActualVariablePaddingEnvelope.projection R V₀ = 𝟙 _)
    (hsg : s ≫ g = ActualVariablePaddingEnvelope.zeroSection R V₁) :
    (principalizationHistory R k V₀ N₀ h₀).pullback (sectionFor R k V₀ N₀ h₀ s hs) =
      basePrincipalizationHistory R k V₁ N₁ h₁ := by
  rw [principalization_eq_pullback R k V₀ V₁ N₀ N₁ h₀ h₁ g hg,← pullback_comp,
    section_compatibility R k V₀ V₁ N₀ N₁ h₀ h₁ g hg s hs hsg]
  rfl
end ActualMap

/-- Two arbitrary valid actual padding choices give EXACTLY the SAME whole genuine ORIGINAL-singular base BP. -/
theorem basePrincipalizationHistories_eq
    (V₁ V₂ : dimensionIndex R → Type u) [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)]
    (N₁ N₂ : ℕ) (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    basePrincipalizationHistory R k V₁ N₁ h₁ = basePrincipalizationHistory R k V₂ N₂ h₂ := by
  let W := commonVariables R k V₁ V₂
  let hW := common_rank R k V₁ V₂ N₁ N₂ h₁ h₂
  let s := commonSection R k V₁ V₂
  have hs : s ≫ ActualVariablePaddingEnvelope.projection R W = 𝟙 _ := by
    rw [← toFirst_projection R k V₁ V₂,← Category.assoc,commonSection_first,
      ActualVariablePaddingEnvelope.zeroSection_projection]
  have : Smooth (toFirst R k V₁ V₂) := by
    have := toFirst_relativeDimension R k V₁ V₂ N₂ h₂
    exact SmoothOfRelativeDimension.smooth N₂ _
  have : Smooth (toSecond R k V₁ V₂) := by
    have := toSecond_relativeDimension R k V₁ V₂ N₁ h₁
    exact SmoothOfRelativeDimension.smooth N₁ _
  have : Surjective (toFirst R k V₁ V₂) := toFirst_surjective R k V₁ V₂
  have : Surjective (toSecond R k V₁ V₂) := toSecond_surjective R k V₁ V₂
  have hfirst := principalization_section_eq R k W V₁ (N₁+N₂) N₁ hW h₁
    (toFirst R k V₁ V₂) (toFirst_projection R k V₁ V₂) s hs (commonSection_first R k V₁ V₂)
  have hsecond := principalization_section_eq R k W V₂ (N₁+N₂) N₂ hW h₂
    (toSecond R k V₁ V₂) (toSecond_projection R k V₁ V₂) s hs (commonSection_second R k V₁ V₂)
  exact hfirst.symm.trans hsecond

/-- Canonical padding gives the SAME original actual descended BP, by genuine whole-BP descent and section retraction. -/
theorem canonicalBasePrincipalization :
    basePrincipalizationHistory R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k) =
      ActualOriginalSingPrincipalizationHistoryDescent.nativeBasePrincipalizationHistory R k := by
  have hp : endpointProjection R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k) =
      ActualPaddedNativePrincipalizationInput.paddedFinalProjection R k := rfl
  have hs := endpointSection_projection R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k)
  rw [hp] at hs
  change (ActualPaddedNativePrincipalizationInput.nativeOriginalSingPrincipalizationHistory R k).pullback
    (endpointSection R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k)) = _
  rw [ActualOriginalSingPrincipalizationHistoryDescent.nativePrincipalization_canonical_history_descends,
    ← pullback_comp,hs,pullback_id]

/-- Every valid actual padding gives EXACTLY the original genuine ORIGINAL-singular base BP. -/
theorem basePrincipalization_eq_original (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    basePrincipalizationHistory R k V N hN =
      ActualOriginalSingPrincipalizationHistoryDescent.nativeBasePrincipalizationHistory R k :=
  (basePrincipalizationHistories_eq R k V (paddingVariables R k) N (commonDimension R k) hN (canonicalRank R k)).trans
    (canonicalBasePrincipalization R k)

/-- Actual assembled original native history for any valid padding, using SAME original separation/A data. -/
def originalHistoryOfPadding (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) : (Spec (.of R)).BlowUpSequence :=
  .cons (Spec (.of R)) (ActualMixedDimensionAffineResolution.separationCentre R)
    (((nativeBaseHistory R k).concat (basePrincipalizationHistory R k V N hN)).pullback
      (ActualMixedDimensionAffineResolution.separationIso R).hom)

/-- Literal equality of ALL actual original centres, map and clock for every genuine padding choice. -/
theorem originalHistoryOfPadding_eq_original (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    originalHistoryOfPadding R k V N hN = ActualMixedDimensionAffineResolution.originalHistory R k := by
  rw [originalHistoryOfPadding,basePrincipalization_eq_original]
  rfl

/-- The genuine original strong resolution, with true ORIGINAL support/Reg, holds for EVERY valid actual padding. -/
theorem originalHistoryOfPadding_isStrongResolution (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (ActualMixedDimensionAffineResolution.originalAlgScheme R k)
      (originalHistoryOfPadding R k V N hN) := by
  rw [originalHistoryOfPadding_eq_original]
  exact ActualMixedDimensionAffineResolution.originalHistory_isStrongResolution R k

end
end Hironaka.Resolution.Algebraic.ActualVariableOriginalSingPrincipalizationChoice
