import Hironaka.Resolution.Algebraic.ActualOriginalSingIdealNonzero
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy

/-!
# ONE principalization on the SAME actual padded native endpoint

Source-first proof: `actual-padded-native-principalization-input-20261102.tex`.
The original uniform dimension extends through the genuine dense inverse
ORIGINAL regular open; smoothness alone never supplies equidimensionality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualPaddedNativePrincipalizationInput

noncomputable section

/-- On a reduced scheme, stalkwise nonzero excludes every nonempty open in the support. -/
theorem dense_compl_support_of_nonzero {X : Scheme.{u}} [IsReduced X]
    (I : X.IdealSheafData) (hI : I.IsNonzeroEverywhere) : Dense (I.support : Set X)ᶜ := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  by_contra h
  have hsub : U ⊆ (I.support : Set X) := by
    intro x hx
    by_contra hxI
    exact h ⟨x,hx,hxI⟩
  let V : X.Opens := ⟨U,hU⟩
  have hres : (I.comap V.ι).IsNonzeroEverywhere := isNonzeroEverywhere_comap_of_flat V.ι hI
  have hsupp : (I.comap V.ι).support = ⊤ := by
    apply top_le_iff.mp
    intro x hx
    rw [support_comap]
    exact hsub x.property
  have hzero : I.comap V.ι = ⊥ := support_eq_top_iff.mp hsupp
  obtain ⟨x,hx⟩ := hUne
  exact hres ⟨x,hx⟩ (by rw [hzero,stalkIdeal_bot])

/-- A smooth morphism inherits the SAME relative dimension from any actual dense open. -/
theorem relativeDimension_of_dense_open {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (U : X.Opens) (hU : Dense (U : Set X)) (n : ℕ)
    [SmoothOfRelativeDimension n (U.ι ≫ f)] : SmoothOfRelativeDimension n f := by
  choose V m hmem hdim using Hironaka.Resolution.exists_smoothOfRelativeDimension_ι_comp f
  have hm : ∀ x, m x = n := by
    intro x
    obtain ⟨w,hwV,hwU⟩ := hU.inter_open_nonempty (V x) (V x).isOpen ⟨x,hmem x⟩
    let W : X.Opens := V x ⊓ U
    have : Nonempty W := ⟨⟨w,hwV,hwU⟩⟩
    have h1 : SmoothOfRelativeDimension (0 + m x)
        (X.homOfLE (inf_le_left : W ≤ V x) ≫ ((V x).ι ≫ f)) := inferInstance
    have h2 : SmoothOfRelativeDimension (0 + n)
        (X.homOfLE (inf_le_right : W ≤ U) ≫ (U.ι ≫ f)) := inferInstance
    rw [Nat.zero_add, ← Category.assoc, Scheme.homOfLE_ι] at h1 h2
    exact SmoothOfRelativeDimension.eq_of_nonempty (W.ι ≫ f)
  have hcover : ⨆ x, V x = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,hmem x⟩
  apply (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension n) V hcover).mpr
  intro x
  rw [← hm x]
  exact hdim x

open ActualDimensionGroupBlowup ActualDimensionGroupRegularLocus ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualOriginalSingIdealNonzero

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

private abbrev originalStructure : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

private instance originalStructure_finiteType : LocallyOfFiniteType (originalStructure R k) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

private abbrev paddedInputStructure : (paddedEnvelope R k).obj.left ⟶ Spec (.of k) :=
  (paddedEnvelope R k).obj.hom

private instance paddedInput_finiteType : FiniteType (paddedInputStructure R k) :=
  (paddedEnvelope R k).obj.prop.1

private instance paddedInput_separated : IsSeparated (paddedInputStructure R k) :=
  (paddedEnvelope R k).obj.prop.2

private instance paddedInput_finitePresentation : LocallyOfFinitePresentation (paddedInputStructure R k) :=
  inferInstance

private instance paddedInput_locallyNoetherian : IsLocallyNoetherian (paddedEnvelope R k).obj.left :=
  LocallyOfFiniteType.isLocallyNoetherian (paddedInputStructure R k)

private instance paddedComposite_proper : IsProper (nativePaddedHistory R k).composite :=
  (nativePaddedHistory R k).isProper_composite

private abbrev paddedEndpointStructure : (nativePaddedHistory R k).last ⟶ Spec (.of k) :=
  (nativePaddedHistory R k).composite ≫ (paddedInputStructure R k)

private instance paddedEndpoint_finiteType : FiniteType (paddedEndpointStructure R k) := by
  dsimp only [paddedEndpointStructure]
  infer_instance

private instance paddedEndpoint_separated : IsSeparated (paddedEndpointStructure R k) := by
  dsimp only [paddedEndpointStructure]
  infer_instance

private instance paddedEndpoint_smooth : Smooth (paddedEndpointStructure R k) :=
  (nativePaddedHistory_isStrongResolution R k).smooth

/-- Actual projection from the SAME native padded endpoint to the canonical base endpoint. -/
def paddedFinalProjection : (nativePaddedHistory R k).last ⟶ (nativeBaseHistory R k).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last
    (nativePaddedHistory_canonical_history_descends R k)) ≫
      (nativeBaseHistory R k).pullbackLastHom (envelopeProjection R k)

/-- The actual final projection lies over the SAME original padded projection. -/
theorem paddedFinalProjection_over :
    paddedFinalProjection R k ≫ (nativeBaseHistory R k).composite =
      (nativePaddedHistory R k).composite ≫ envelopeProjection R k := by
  rw [paddedFinalProjection, Category.assoc, pullbackLastHom_comp_composite,
    ← Category.assoc]
  exact congrArg (fun h => h ≫ envelopeProjection R k)
    (eqToHom_comp_composite_of_eq (nativePaddedHistory_canonical_history_descends R k))

/-- Actual flat base change and literal SAME-history transport derive smoothness of this projection. -/
theorem paddedFinalProjection_smooth : Smooth (paddedFinalProjection R k) := by
  have : Smooth (envelopeProjection R k) := envelopeProjection_smooth R k
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (smooth_pullbackLastHom (nativeBaseHistory R k) (envelopeProjection R k))

/-- The genuine ORIGINAL singular ideal on the SAME actual native padded endpoint. -/
def paddedFinalOriginalSing : (nativePaddedHistory R k).last.IdealSheafData :=
  (Spec (.of R)).singIdeal.comap ((nativePaddedHistory R k).composite ≫
    envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R))

/-- Flat pullback along the actual final projection gives genuine ORIGINAL-ideal nonvanishing. -/
theorem paddedFinalOriginalSing_nonzero : (paddedFinalOriginalSing R k).IsNonzeroEverywhere := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  have hnz := isNonzeroEverywhere_comap_of_flat (paddedFinalProjection R k)
    (originalSingPullback_nonzero R k)
  have heq : paddedFinalOriginalSing R k = (originalSingPullback R k).comap (paddedFinalProjection R k) := by
    change (Spec (.of R)).singIdeal.comap ((nativePaddedHistory R k).composite ≫
      envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R)) = _
    rw [originalSingPullback, ← comap_comp]
    apply congrArg (Spec (.of R)).singIdeal.comap
    simpa only [Category.assoc] using
      (congrArg (fun h => h ≫ affineBlowUp.π (dimensionSeparationIdeal R))
        (paddedFinalProjection_over R k).symm)
  exact heq.symm ▸ hnz

/-- The actual inverse ENTIRE ORIGINAL regular open in the SAME padded endpoint. -/
def paddedFinalOriginalRegularOpen : (nativePaddedHistory R k).last.Opens :=
  ((nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
    affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ (originalStructure R k).smoothLocus

/-- This actual inverse ORIGINAL regular open is dense; no component-survival certificate is assumed. -/
theorem paddedFinalOriginalRegularOpen_dense :
    Dense (paddedFinalOriginalRegularOpen R k : Set (nativePaddedHistory R k).last) := by
  have : IsReduced (nativePaddedHistory R k).last :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (paddedEndpointStructure R k)
  have hd := dense_compl_support_of_nonzero (paddedFinalOriginalSing R k)
    (paddedFinalOriginalSing_nonzero R k)
  have hsupp : ((paddedFinalOriginalSing R k).support : Set (nativePaddedHistory R k).last) =
      (paddedFinalOriginalRegularOpen R k : Set (nativePaddedHistory R k).last)ᶜ := by
    rw [paddedFinalOriginalSing, support_comap, Closeds.coe_preimage,
      Scheme.coe_support_singIdeal_eq_singularLocus (originalStructure R k),
      Scheme.singularLocus_eq_compl_smoothLocus (originalStructure R k)]
    rfl
  rw [hsupp, compl_compl] at hd
  exact hd

private theorem paddedOriginalRegular_le_smoothLocus :
    (envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ
      (originalStructure R k).smoothLocus ≤ (paddedInputStructure R k).smoothLocus := by
  let U := (originalStructure R k).smoothLocus
  let g := envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R)
  let V := g ⁻¹ᵁ U
  have : Smooth (envelopeProjection R k) := envelopeProjection_smooth R k
  have : IsIso (affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U) :=
    separation_isIso_over_smoothLocus R k
  have : Smooth (U.ι ≫ originalStructure R k) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact U.ι_preimage_self
  have hcomp : Smooth (g ∣_ U ≫ U.ι ≫ originalStructure R k) := by
    rw [show g ∣_ U = envelopeProjection R k ∣_
        (affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ U ≫
        affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U from morphismRestrict_comp _ _ _]
    infer_instance
  have : Smooth (V.ι ≫ (paddedInputStructure R k)) := by
    have he : g ∣_ U ≫ U.ι ≫ originalStructure R k =
        V.ι ≫ (paddedInputStructure R k) := by
      rw [← Category.assoc, morphismRestrict_ι]
      rfl
    exact he ▸ hcomp
  intro x hx
  exact ((paddedInputStructure R k).mem_smoothLocus_iff_exists_smooth).mpr ⟨V,hx,inferInstance⟩

/-- ONE SAME original uniform relative dimension holds before and after the ONE native history. -/
theorem nativePaddedEndpoint_same_dimension : ∃ n : ℕ,
    SmoothOfRelativeDimension n ((paddedInputStructure R k).smoothLocus.ι ≫
      (paddedInputStructure R k)) ∧ SmoothOfRelativeDimension n (paddedEndpointStructure R k) := by
  obtain ⟨n,hn⟩ := (paddedEnvelope R k).property.2
  have : SmoothOfRelativeDimension n (((paddedInputStructure R k)).smoothLocus.ι ≫
      (paddedInputStructure R k)) := hn
  refine ⟨n,hn,?_⟩
  let W := paddedFinalOriginalRegularOpen R k
  have hle : W ≤ (nativePaddedHistory R k).composite ⁻¹ᵁ (paddedInputStructure R k).smoothLocus := by
    intro x hx
    exact paddedOriginalRegular_le_smoothLocus R k hx
  have : IsIso ((nativePaddedHistory R k).composite ∣_ (paddedInputStructure R k).smoothLocus) :=
    (nativePaddedHistory_isStrongResolution R k).isIso_restrict_smoothLocus
  have : IsOpenImmersion ((nativePaddedHistory R k).composite.resLE
      (paddedInputStructure R k).smoothLocus W hle) := by
    dsimp only [Scheme.Hom.resLE]
    infer_instance
  have : SmoothOfRelativeDimension n ((nativePaddedHistory R k).composite.resLE
      (paddedInputStructure R k).smoothLocus W hle ≫
      ((paddedInputStructure R k).smoothLocus.ι ≫ (paddedInputStructure R k))) := by
    have : SmoothOfRelativeDimension (0 + n) ((nativePaddedHistory R k).composite.resLE
        (paddedInputStructure R k).smoothLocus W hle ≫
        ((paddedInputStructure R k).smoothLocus.ι ≫ (paddedInputStructure R k))) := inferInstance
    simpa only [Nat.zero_add] using this
  have : SmoothOfRelativeDimension n (W.ι ≫ paddedEndpointStructure R k) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc] at this
    exact this
  exact relativeDimension_of_dense_open (paddedEndpointStructure R k) W
    (paddedFinalOriginalRegularOpen_dense R k) n

/-- Internally constructed genuine native triple on the SAME actual padded endpoint and ORIGINAL ideal. -/
def nativeOriginalSingPrincipalizationTriple : Triple k where
  X := .ofHom (paddedEndpointStructure R k) inferInstance inferInstance
  smoothOfRelativeDimension := by
    obtain ⟨n,-,hn⟩ := nativePaddedEndpoint_same_dimension R k
    exact ⟨n,hn⟩
  I := paddedFinalOriginalSing R k
  isNonzeroEverywhere := paddedFinalOriginalSing_nonzero R k
  E := Scheme.DivisorFamily.empty _
  isSnc := isSnc_empty_of_smooth (paddedEndpointStructure R k)

/-- ONE deterministic native principalization of the genuine ORIGINAL ideal on the SAME endpoint. -/
def nativeOriginalSingPrincipalizationHistory : (nativePaddedHistory R k).last.BlowUpSequence :=
  BP (nativeOriginalSingPrincipalizationTriple R k)

/-- The ORIGINAL ideal's actual inverse image is SNC on this ONE padded principalization endpoint. -/
theorem nativeOriginalSingPrincipalization_isSNC :
    Scheme.IdealSheafData.IsIdealOfSncDivisor ((paddedFinalOriginalSing R k).comap
      (nativeOriginalSingPrincipalizationHistory R k).composite) :=
  BP_isIdealOfSncDivisor (nativeOriginalSingPrincipalizationTriple R k)
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualPaddedNativePrincipalizationInput
