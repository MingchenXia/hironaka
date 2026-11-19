import Hironaka.Resolution.Algebraic.ActualGlobalPrincipalizedEndpoint

/-!
# ONE actual strong resolution of the ORIGINAL global mixed-dimensional input

Source-first proof: `actual-global-mixed-dimension-resolution-20261102.tex`.
The actual global separation and SAME two descended histories form one native
sequence with its entire original clock and true ORIGINAL singular support.
Smooth/field compatibility and canonical ALG13 remain OPEN.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalMixedDimensionResolution

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingPrincipalizationInput ActualGlobalOriginalSingPrincipalizationHistoryDescent
  ActualGlobalPrincipalizedEndpoint ActualGlobalDimensionClopenPartition
  ActualGlobalOriginalRegularGeometry ActualHistoryOriginalRegularIsomorphism

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    (V : dimensionIndex X → Type u) [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)

theorem basePrincipalization_isIso_original_regular :
    IsIso ((basePrincipalizationHistory p V N hN).composite ∣_
      ((baseHistory p V N hN).composite ≫ separationProjection X) ⁻¹ᵁ p.smoothLocus) := by
  have : Smooth (endpointProjection p V N hN) := endpointProjection_smooth p V N hN
  let T := originalTriple p V N hN
  have : IsIso ((principalizationHistory p V N hN).composite ∣_
      (T.I.support ⊔ T.E.singularLocus).compl) := BP_isIso_restrict T
  have hEmpty : T.E.singularLocus = ⊥ := by
    change (Scheme.DivisorFamily.empty (history p V N hN).last).singularLocus = ⊥
    simp [Scheme.DivisorFamily.singularLocus, Scheme.DivisorFamily.empty]
  have hle : (endpointProjection p V N hN) ⁻¹ᵁ
      ((baseHistory p V N hN).composite ≫ separationProjection X) ⁻¹ᵁ p.smoothLocus ≤
        (T.I.support ⊔ T.E.singularLocus).compl := by
    intro x hx
    rw [hEmpty, sup_bot_eq]
    change x ∉ ((originalIdeal p V N hN).support : Set (history p V N hN).last)
    rw [originalIdeal_support, Scheme.singularLocus_eq_compl_smoothLocus p]
    change ¬ separationProjection X (projection X V ((history p V N hN).composite x)) ∈
      (p.smoothLocus : Set X)ᶜ
    have he := congrArg (fun g => separationProjection X (g x)) (endpointProjection_over p V N hN)
    simp only [Scheme.Hom.comp_apply] at he
    change separationProjection X ((baseHistory p V N hN).composite (endpointProjection p V N hN x)) ∈
      p.smoothLocus at hx
    exact fun h => h (he ▸ hx)
  have : IsIso ((principalizationHistory p V N hN).composite ∣_ (endpointProjection p V N hN) ⁻¹ᵁ
      ((baseHistory p V N hN).composite ≫ separationProjection X) ⁻¹ᵁ p.smoothLocus) :=
    isIso_restrict_of_le _ hle
  exact isIso_restrict_of_split_cartesian (principalized_isPullback p V N hN)
    (endpointSection p V N hN) (endpointSection_projection p V N hN) _

/-- ONE actual original global history, retaining the first centre and both complete clocks. -/
def originalHistory : X.BlowUpSequence :=
  .cons X (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
    ((baseHistory p V N hN).concat (basePrincipalizationHistory p V N hN))

theorem originalHistory_length : (originalHistory p V N hN).length =
    (baseHistory p V N hN).length + (basePrincipalizationHistory p V N hN).length + 1 :=
  congrArg (· + 1) (length_concat (baseHistory p V N hN) (basePrincipalizationHistory p V N hN))

def originalEndpointIso : (originalHistory p V N hN).last ≅ (basePrincipalizationHistory p V N hN).last :=
  eqToIso (last_concat (baseHistory p V N hN) (basePrincipalizationHistory p V N hN))

theorem originalHistory_composite : (originalHistory p V N hN).composite =
    (originalEndpointIso p V N hN).hom ≫ (basePrincipalizationHistory p V N hN).composite ≫
      (baseHistory p V N hN).composite ≫ separationProjection X := by
  change ((baseHistory p V N hN).concat (basePrincipalizationHistory p V N hN)).composite ≫
    separationProjection X = _
  rw [composite_concat]
  rfl

theorem originalHistory_isProjective : IsProjective (originalHistory p V N hN).composite :=
  (originalHistory p V N hN).isProjective_composite

theorem originalHistory_isProper : IsProper (originalHistory p V N hN).composite :=
  (originalHistory p V N hN).isProper_composite

private abbrev finalBaseStructure : (basePrincipalizationHistory p V N hN).last ⟶ Spec (.of k) :=
  (basePrincipalizationHistory p V N hN).composite ≫ baseStructure p V N hN

private instance finalBaseStructure_smooth : Smooth (finalBaseStructure p V N hN) :=
  principalizedBase_smooth p V N hN

theorem originalHistory_smooth : Smooth ((originalHistory p V N hN).composite ≫ p) := by
  have he : (originalHistory p V N hN).composite ≫ p =
      (originalEndpointIso p V N hN).hom ≫ finalBaseStructure p V N hN := by
    rw [originalHistory_composite]
    rfl
  rw [he]
  infer_instance

theorem originalHistory_isIso_over_regular : IsIso ((originalHistory p V N hN).composite ∣_ p.smoothLocus) := by
  let U := p.smoothLocus
  have : IsIso (separationProjection X ∣_ U) := separation_isIso_original_regular p
  have : IsIso ((baseHistory p V N hN).composite ∣_ (separationProjection X) ⁻¹ᵁ U) :=
    baseHistory_isIso_original_regular p V N hN
  have : IsIso (((baseHistory p V N hN).composite ≫ separationProjection X) ∣_ U) :=
    isIso_restrict_comp _ _ U
  have : IsIso ((basePrincipalizationHistory p V N hN).composite ∣_
      ((baseHistory p V N hN).composite ≫ separationProjection X) ⁻¹ᵁ U) :=
    basePrincipalization_isIso_original_regular p V N hN
  have : IsIso (((basePrincipalizationHistory p V N hN).composite ≫
      (baseHistory p V N hN).composite ≫ separationProjection X) ∣_ U) := isIso_restrict_comp _ _ U
  have : IsIso (((originalEndpointIso p V N hN).hom ≫ (basePrincipalizationHistory p V N hN).composite ≫
      (baseHistory p V N hN).composite ≫ separationProjection X) ∣_ U) := isIso_restrict_comp _ _ U
  exact isIso_restrict_congr (originalHistory_composite p V N hN).symm U

private instance originalStructure_finiteType : FiniteType p := inferInstance

def originalAlgScheme : AlgScheme k := .ofHom p inferInstance inferInstance

private instance originalAlgScheme_noetherian : IsNoetherian (originalAlgScheme p).left := by
  change IsNoetherian X
  infer_instance

private instance originalAlgScheme_reduced : IsReduced (originalAlgScheme p).left := by
  change IsReduced X
  infer_instance

theorem originalHistory_originalSing_isSnc : Scheme.IsSncDivisor
    ((originalHistory p V N hN).composite ⁻¹' (p.smoothLocus : Set X)ᶜ) := by
  refine ⟨(baseBoundary p V N hN).comap (originalEndpointIso p V N hN).hom, ?_, ?_⟩
  · exact isSnc_comap_of_smooth (finalBaseStructure p V N hN) (originalEndpointIso p V N hN).hom
      (baseBoundary_isSnc p V N hN)
  · rw [Hironaka.Resolution.coe_support_comap, baseBoundary_original_support, principalizedOriginalIdeal,
      support_comap, Closeds.coe_preimage, Scheme.coe_support_singIdeal_eq_singularLocus p,
      Scheme.singularLocus_eq_compl_smoothLocus p, originalHistory_composite]
    rfl

theorem originalHistory_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (originalAlgScheme p) (originalHistory p V N hN) := by
  have hreg : IsIso ((originalHistory p V N hN).composite ∣_ p.smoothLocus) := originalHistory_isIso_over_regular p V N hN
  refine ⟨⟨originalHistory_smooth p V N hN, originalHistory_isProjective p V N hN,
    p.smoothLocus, p.dense_smoothLocus_of_perfectField, hreg⟩,
    hreg, originalHistory_originalSing_isSnc p V N hN⟩

abbrev canonicalOriginalHistory := originalHistory p (paddingVariables p) (commonDimension p) (padding_rank p)

theorem canonicalOriginalHistory_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (originalAlgScheme p) (canonicalOriginalHistory p) :=
  originalHistory_isStrongResolution p (paddingVariables p) (commonDimension p) (padding_rank p)

theorem exists_original_strong_resolution : ∃ S : X.BlowUpSequence,
    @Scheme.BlowUpSequence.IsStrongResolution k _ (originalAlgScheme p) S :=
  ⟨canonicalOriginalHistory p, canonicalOriginalHistory_isStrongResolution p⟩

end
end Hironaka.Resolution.Algebraic.ActualGlobalMixedDimensionResolution
