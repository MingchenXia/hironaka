import Hironaka.Resolution.Algebraic.ActualGlobalPaddingResolutionChoice
import Hironaka.Resolution.Algebraic.ActualVariableOriginalSingPrincipalizationChoice

/-!
# The SAME actual global ORIGINAL history is independent of actual padding

Source-first proof: `actual-global-padding-principalization-choice-20261102.tex`.
Actual native endpoint squares and complete-blowup uniqueness compare ONE common
BP through ONE genuine common section over the SAME canonical base endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalPaddingPrincipalizationChoice

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity ActualGlobalDimensionClopenPartition
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingPrincipalizationInput ActualGlobalPaddingResolutionChoice ActualPaddedEnvelopeNativeTranslations
open ActualVariableOriginalSingPrincipalizationChoice (composite_hom_ext_of_flat)

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
  {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]

omit [IsReduced X] [CharZero k] [IsSeparated p] in
include p in
private theorem base_noetherian : IsNoetherian (separationSpace X) := by
  have : FiniteType p := inferInstance
  have : IsProper (separationProjection X) := ActualGlobalSeparationAffineCharts.separationProjection_isProper
  let f := separationStructure p
  have : LocallyOfFiniteType f := inferInstance
  have : QuasiCompact f := by dsimp only [f, separationStructure]; infer_instance
  exact f.isNoetherian_of_field

section ActualEndpoint
variable (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
  (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

def normalizedEndpointProjection : (history p V N hN).last ⟶ (canonicalBaseHistory p).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (history_canonical_descends p V N hN)) ≫
    (canonicalBaseHistory p).pullbackLastHom (projection X V)

theorem normalizedEndpoint_isPullback : IsPullback (normalizedEndpointProjection p V N hN)
    (history p V N hN).composite (canonicalBaseHistory p).composite (projection X V) := by
  have : Smooth (projection X V) := projection_smooth X V
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq (canonicalBaseHistory p)
    (projection X V) (history p V N hN) (history_canonical_descends p V N hN)

theorem normalizedEndpointProjection_over : normalizedEndpointProjection p V N hN ≫ (canonicalBaseHistory p).composite =
    (history p V N hN).composite ≫ projection X V := (normalizedEndpoint_isPullback p V N hN).w

theorem normalizedEndpointProjection_smooth : Smooth (normalizedEndpointProjection p V N hN) :=
  property_of_isPullback _ (normalizedEndpoint_isPullback p V N hN) (projection_smooth X V)
end ActualEndpoint


/-- Real final cartesian lift of ANY actual original input section. -/
def sectionFor (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)
    (s : separationSpace X ⟶ ActualGlobalVariablePaddingGeometry.envelope X V)
    (hs : s ≫ ActualGlobalVariablePaddingGeometry.projection X V = 𝟙 _) :
    (canonicalBaseHistory p).last ⟶ (history p V N hN).last :=
  (normalizedEndpoint_isPullback p V N hN).lift (𝟙 _) ((canonicalBaseHistory p).composite ≫ s) (by simp [hs])

/-- Actual final retraction for the genuine cartesian lift. -/
theorem sectionFor_projection (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)
    (s : separationSpace X ⟶ ActualGlobalVariablePaddingGeometry.envelope X V)
    (hs : s ≫ ActualGlobalVariablePaddingGeometry.projection X V = 𝟙 _) :
    sectionFor p V N hN s hs ≫ normalizedEndpointProjection p V N hN = 𝟙 _ :=
  (normalizedEndpoint_isPullback p V N hN).lift_fst _ _ _

/-- Genuine original-input equation for the same actual final lift. -/
theorem sectionFor_original (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)
    (s : separationSpace X ⟶ ActualGlobalVariablePaddingGeometry.envelope X V)
    (hs : s ≫ ActualGlobalVariablePaddingGeometry.projection X V = 𝟙 _) :
    sectionFor p V N hN s hs ≫ (history p V N hN).composite = (canonicalBaseHistory p).composite ≫ s :=
  (normalizedEndpoint_isPullback p V N hN).lift_snd _ _ _

def normalizedEndpointSection (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    (canonicalBaseHistory p).last ⟶ (history p V N hN).last :=
  sectionFor p V N hN (zeroSection X V) (zeroSection_projection X V)

theorem normalizedEndpointSection_projection (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    normalizedEndpointSection p V N hN ≫ normalizedEndpointProjection p V N hN = 𝟙 _ :=
  sectionFor_projection p V N hN (zeroSection X V) (zeroSection_projection X V)

theorem normalizedEndpointSection_original (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    normalizedEndpointSection p V N hN ≫ (history p V N hN).composite =
      (canonicalBaseHistory p).composite ≫ zeroSection X V :=
  sectionFor_original p V N hN (zeroSection X V) (zeroSection_projection X V)

/-- The actual base BP through its genuine final original-zero section. -/
def normalizedBasePrincipalizationHistory (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) : (canonicalBaseHistory p).last.BlowUpSequence :=
  (principalizationHistory p V N hN).pullback (normalizedEndpointSection p V N hN)

section ActualMap
variable (V₀ V₁ : dimensionIndex X → Type u) [∀ d, Finite (V₀ d)] [∀ d, Finite (V₁ d)]
  (N₀ N₁ : ℕ) (h₀ : ∀ d, dimensionNat p d + Nat.card (V₀ d) = N₀)
  (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
  (g : ActualGlobalVariablePaddingGeometry.envelope X V₀ ⟶ ActualGlobalVariablePaddingGeometry.envelope X V₁)
  [Smooth g] [Surjective g]
  (hg : g ≫ ActualGlobalVariablePaddingGeometry.projection X V₁ = ActualGlobalVariablePaddingGeometry.projection X V₀)

private def inputMap : ActualGlobalPaddedNativeInput.variableEnvelope p V₀ N₀ h₀ ⟶
    ActualGlobalPaddedNativeInput.variableEnvelope p V₁ N₁ h₁ :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk g (by
    change g ≫ (ActualGlobalVariablePaddingGeometry.projection X V₁ ≫ separationProjection X ≫
      p) = _
    rw [← Category.assoc,hg]
    rfl))

include hg in
private theorem resolutionEq : history p V₀ N₀ h₀ = (history p V₁ N₁ h₁).pullback g := by
  let f := inputMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg
  have hs : Smooth (HasUnderlyingScheme.hom f) := by
    change Smooth g
    infer_instance
  have hsurj : Function.Surjective (HasUnderlyingScheme.hom f) := by
    change Function.Surjective g
    exact (inferInstance : Surjective g).1
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective f hs hsurj

def nativeEndpointMap : (history p V₀ N₀ h₀).last ⟶ (history p V₁ N₁ h₁).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (resolutionEq p V₀ V₁ N₀ N₁ h₀ h₁ g hg)) ≫
    (history p V₁ N₁ h₁).pullbackLastHom g

private theorem endpointMap_square : IsPullback (nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg)
    (history p V₀ N₀ h₀).composite (history p V₁ N₁ h₁).composite g :=
  ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq (history p V₁ N₁ h₁) g
    (history p V₀ N₀ h₀) (resolutionEq p V₀ V₁ N₀ N₁ h₀ h₁ g hg)

private theorem endpointMap_over : nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg ≫ (history p V₁ N₁ h₁).composite =
    (history p V₀ N₀ h₀).composite ≫ g := (endpointMap_square p V₀ V₁ N₀ N₁ h₀ h₁ g hg).w

private theorem endpointMap_smooth : Smooth (nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg) :=
  property_of_isPullback _ (endpointMap_square p V₀ V₁ N₀ N₁ h₀ h₁ g hg) (inferInstance : Smooth g)

private theorem endpointMap_surjective : Surjective (nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg) :=
  property_of_isPullback _ (endpointMap_square p V₀ V₁ N₀ N₁ h₀ h₁ g hg) (inferInstance : Surjective g)

private theorem endpointMap_projection : nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg ≫ normalizedEndpointProjection p V₁ N₁ h₁ =
    normalizedEndpointProjection p V₀ N₀ h₀ := by
  have : IsNoetherian (separationSpace X) := base_noetherian p
  have : Smooth (normalizedEndpointProjection p V₀ N₀ h₀) := normalizedEndpointProjection_smooth p V₀ N₀ h₀
  apply composite_hom_ext_of_flat (canonicalBaseHistory p)
  calc
    _ = nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg ≫
        ((history p V₁ N₁ h₁).composite ≫ ActualGlobalVariablePaddingGeometry.projection X V₁) := by
      rw [Category.assoc,normalizedEndpointProjection_over]
    _ = ((history p V₀ N₀ h₀).composite ≫ g) ≫ ActualGlobalVariablePaddingGeometry.projection X V₁ := by
      rw [← Category.assoc,endpointMap_over]
    _ = (history p V₀ N₀ h₀).composite ≫ ActualGlobalVariablePaddingGeometry.projection X V₀ := by
      rw [Category.assoc,hg]
    _ = normalizedEndpointProjection p V₀ N₀ h₀ ≫ (canonicalBaseHistory p).composite :=
      (normalizedEndpointProjection_over p V₀ N₀ h₀).symm

theorem principalization_eq_pullback : principalizationHistory p V₀ N₀ h₀ =
    (principalizationHistory p V₁ N₁ h₁).pullback (nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg) := by
  let m := nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg
  let T₀ := originalTriple p V₀ N₀ h₀
  let T₁ := originalTriple p V₁ N₁ h₁
  have : Smooth m := endpointMap_smooth p V₀ V₁ N₀ N₁ h₀ h₁ g hg
  have he : m ≫ ((history p V₁ N₁ h₁).composite ≫ ActualGlobalVariablePaddingGeometry.projection X V₁) =
      (history p V₀ N₀ h₀).composite ≫ ActualGlobalVariablePaddingGeometry.projection X V₀ := by
    rw [← Category.assoc,endpointMap_over,Category.assoc,hg]
  have hf : m ≫ (T₁.X.left ↘ Spec (.of k)) = T₀.X.left ↘ Spec (.of k) := by
    change m ≫ ((history p V₁ N₁ h₁).composite ≫ ActualGlobalVariablePaddingGeometry.projection X V₁ ≫
      separationProjection X ≫ p) =
        (history p V₀ N₀ h₀).composite ≫ ActualGlobalVariablePaddingGeometry.projection X V₀ ≫
          separationProjection X ≫ p
    simpa only [Category.assoc] using congrArg (fun f => f ≫ separationProjection X ≫
      p) he
  have hI : T₀.I = T₁.I.comap m := by
    change originalIdeal p V₀ N₀ h₀ = (originalIdeal p V₁ N₁ h₁).comap m
    rw [originalIdeal,originalIdeal,← comap_comp]
    apply congrArg X.singIdeal.comap
    simpa only [Category.assoc] using (congrArg (fun f => f ≫ separationProjection X) he).symm
  have hE : T₀.E = T₁.E.comap m := (empty_comap m).symm
  exact BP_pullback_of_surjective T₁ T₀ m (endpointMap_surjective p V₀ V₁ N₀ N₁ h₀ h₁ g hg).1 ⟨hf,hI,hE⟩

private theorem section_compatibility
    (s : separationSpace X ⟶ ActualGlobalVariablePaddingGeometry.envelope X V₀)
    (hs : s ≫ ActualGlobalVariablePaddingGeometry.projection X V₀ = 𝟙 _)
    (hsg : s ≫ g = ActualGlobalVariablePaddingGeometry.zeroSection X V₁) :
    sectionFor p V₀ N₀ h₀ s hs ≫ nativeEndpointMap p V₀ V₁ N₀ N₁ h₀ h₁ g hg = normalizedEndpointSection p V₁ N₁ h₁ := by
  apply (normalizedEndpoint_isPullback p V₁ N₁ h₁).hom_ext
  · rw [Category.assoc,endpointMap_projection,sectionFor_projection,normalizedEndpointSection_projection]
  · rw [Category.assoc,endpointMap_over,← Category.assoc,sectionFor_original,Category.assoc,hsg,
      normalizedEndpointSection_original]

include hg in
private theorem principalization_section_eq
    (s : separationSpace X ⟶ ActualGlobalVariablePaddingGeometry.envelope X V₀)
    (hs : s ≫ ActualGlobalVariablePaddingGeometry.projection X V₀ = 𝟙 _)
    (hsg : s ≫ g = ActualGlobalVariablePaddingGeometry.zeroSection X V₁) :
    (principalizationHistory p V₀ N₀ h₀).pullback (sectionFor p V₀ N₀ h₀ s hs) =
      normalizedBasePrincipalizationHistory p V₁ N₁ h₁ := by
  rw [principalization_eq_pullback p V₀ V₁ N₀ N₁ h₀ h₁ g hg,← pullback_comp,
    section_compatibility p V₀ V₁ N₀ N₁ h₀ h₁ g hg s hs hsg]
  rfl
end ActualMap

/-- Two arbitrary valid actual padding choices give EXACTLY the SAME whole genuine ORIGINAL-singular base BP. -/
theorem normalizedBasePrincipalizationHistories_eq
    (V₁ V₂ : dimensionIndex X → Type u) [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)]
    (N₁ N₂ : ℕ) (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    normalizedBasePrincipalizationHistory p V₁ N₁ h₁ = normalizedBasePrincipalizationHistory p V₂ N₂ h₂ := by
  let W := commonVariables p V₁ V₂
  let hW := common_rank p V₁ V₂ N₁ N₂ h₁ h₂
  let s := commonSection p V₁ V₂
  have hs : s ≫ ActualGlobalVariablePaddingGeometry.projection X W = 𝟙 _ := by
    rw [← toFirst_projection p V₁ V₂,← Category.assoc,commonSection_first,
      ActualGlobalVariablePaddingGeometry.zeroSection_projection]
  have : Smooth (toFirst p V₁ V₂) := by
    have := toFirst_relativeDimension p V₁ V₂ N₂ h₂
    exact SmoothOfRelativeDimension.smooth N₂ _
  have : Smooth (toSecond p V₁ V₂) := by
    have := toSecond_relativeDimension p V₁ V₂ N₁ h₁
    exact SmoothOfRelativeDimension.smooth N₁ _
  have : Surjective (toFirst p V₁ V₂) := toFirst_surjective p V₁ V₂
  have : Surjective (toSecond p V₁ V₂) := toSecond_surjective p V₁ V₂
  have hfirst := principalization_section_eq p W V₁ (N₁+N₂) N₁ hW h₁
    (toFirst p V₁ V₂) (toFirst_projection p V₁ V₂) s hs (commonSection_first p V₁ V₂)
  have hsecond := principalization_section_eq p W V₂ (N₁+N₂) N₂ hW h₂
    (toSecond p V₁ V₂) (toSecond_projection p V₁ V₂) s hs (commonSection_second p V₁ V₂)
  exact hfirst.symm.trans hsecond

/-- Actual canonical normalization is exactly the already constructed canonical whole global BP. -/
theorem canonicalBasePrincipalization :
    normalizedBasePrincipalizationHistory p (paddingVariables p) (commonDimension p) (padding_rank p) =
      ActualGlobalOriginalSingPrincipalizationHistoryDescent.basePrincipalizationHistory p
        (paddingVariables p) (commonDimension p) (padding_rank p) := by
  rfl

/-- Every valid padding gives the SAME actual canonical ORIGINAL-singular BP with its complete clock. -/
theorem normalizedBasePrincipalization_eq_canonical (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    normalizedBasePrincipalizationHistory p V N hN =
      ActualGlobalOriginalSingPrincipalizationHistoryDescent.basePrincipalizationHistory p
        (paddingVariables p) (commonDimension p) (padding_rank p) :=
  (normalizedBasePrincipalizationHistories_eq p V (paddingVariables p) N (commonDimension p) hN (padding_rank p)).trans
    (canonicalBasePrincipalization p)

/-- The actual original separation followed by the SAME canonical base and the actual padding's ONE BP. -/
def originalHistoryOfPadding (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) : X.BlowUpSequence :=
  .cons X (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
    ((canonicalBaseHistory p).concat (normalizedBasePrincipalizationHistory p V N hN))

/-- The original OWN-base sequence is literally the actual canonical-base presentation. -/
theorem originalHistory_eq_historyOfPadding (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    ActualGlobalMixedDimensionResolution.originalHistory p V N hN = originalHistoryOfPadding p V N hN := by
  have : Smooth (projection X V) := projection_smooth X V
  let Ψ : (A : (separationSpace X).BlowUpSequence) →
      (history p V N hN = A.pullback (projection X V)) → (separationSpace X).BlowUpSequence := fun A h =>
    A.concat ((principalizationHistory p V N hN).pullback
      ((ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq A (projection X V)
        (history p V N hN) h).lift (𝟙 _) (A.composite ≫ zeroSection X V)
          (by simp [zeroSection_projection])))
  have hfun : ∀ (A A' : (separationSpace X).BlowUpSequence) (e : A = A')
      (h : history p V N hN = A.pullback (projection X V))
      (h' : history p V N hN = A'.pullback (projection X V)), Ψ A h = Ψ A' h' := by
    intro A A' e h h'
    subst A'
    rfl
  have htail : (baseHistory p V N hN).concat
      (ActualGlobalOriginalSingPrincipalizationHistoryDescent.basePrincipalizationHistory p V N hN) =
        (canonicalBaseHistory p).concat (normalizedBasePrincipalizationHistory p V N hN) := by
    change Ψ (baseHistory p V N hN) (history_descends p V N hN) =
      Ψ (canonicalBaseHistory p) (history_canonical_descends p V N hN)
    exact hfun _ _ (baseHistory_eq_canonical p V N hN)
      (history_descends p V N hN) (history_canonical_descends p V N hN)
  exact congrArg (Scheme.BlowUpSequence.cons X (ActualGlobalDimensionSeparationIdeal.separationIdeal X)) htail

/-- All actual original centres and native clock positions coincide exactly with the canonical history. -/
theorem originalHistoryOfPadding_eq_canonical (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    originalHistoryOfPadding p V N hN = ActualGlobalMixedDimensionResolution.canonicalOriginalHistory p := by
  rw [originalHistoryOfPadding, normalizedBasePrincipalization_eq_canonical]
  rfl

/-- Every actual original OWN-base history has the SAME original centres and complete clock. -/
theorem originalHistory_eq_canonical (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    ActualGlobalMixedDimensionResolution.originalHistory p V N hN =
      ActualGlobalMixedDimensionResolution.canonicalOriginalHistory p :=
  (originalHistory_eq_historyOfPadding p V N hN).trans (originalHistoryOfPadding_eq_canonical p V N hN)

private instance originalAlgScheme_noetherian :
    IsNoetherian (ActualGlobalMixedDimensionResolution.originalAlgScheme p).left := by
  change IsNoetherian X
  infer_instance

private instance originalAlgScheme_reduced :
    IsReduced (ActualGlobalMixedDimensionResolution.originalAlgScheme p).left := by
  change IsReduced X
  infer_instance

/-- Actual ORIGINAL strong resolution with genuine original Reg and Sing for every valid actual padding. -/
theorem originalHistoryOfPadding_isStrongResolution (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (ActualGlobalMixedDimensionResolution.originalAlgScheme p)
      (originalHistoryOfPadding p V N hN) := by
  rw [originalHistoryOfPadding_eq_canonical]
  exact ActualGlobalMixedDimensionResolution.canonicalOriginalHistory_isStrongResolution p

end
end Hironaka.Resolution.Algebraic.ActualGlobalPaddingPrincipalizationChoice
