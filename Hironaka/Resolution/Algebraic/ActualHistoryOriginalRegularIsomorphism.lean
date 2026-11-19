import Hironaka.Resolution.Algebraic.ActualSplitSncReflection
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.IsoLocus

/-!
# SAME actual descended histories preserve the ENTIRE ORIGINAL regular locus

Source-first proof: `actual-history-original-regular-isomorphism-20261102.tex`.
Isomorphism reflection uses genuine cartesian squares and actual sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualHistoryOriginalRegularIsomorphism

noncomputable section

/-- Genuine inverse construction reflects an isomorphism through an actual split cartesian square. -/
theorem isIso_of_split_cartesian {C : Type*} [Category C] {W Y E X : C}
    {p : W ⟶ Y} {u : W ⟶ E} {f : Y ⟶ X} {q : E ⟶ X}
    (H : IsPullback p u f q) (s : X ⟶ E) (hs : s ≫ q = 𝟙 X) [IsIso u] : IsIso f := by
  let t := H.lift (𝟙 Y) (f ≫ s) (by simp [hs])
  have htp : t ≫ p = 𝟙 Y := H.lift_fst _ _ _
  have htu : t ≫ u = f ≫ s := H.lift_snd _ _ _
  let i := s ≫ inv u ≫ p
  have hi : i ≫ f = 𝟙 X := by
    dsimp only [i]
    simp only [Category.assoc,H.w,IsIso.inv_hom_id_assoc,hs]
  have hf : f ≫ i = 𝟙 Y := by
    dsimp only [i]
    rw [← Category.assoc,← htu,Category.assoc,IsIso.hom_inv_id_assoc,htp]
  exact ⟨⟨i,hf,hi⟩⟩

/-- Actual open restrictions retain the split cartesian isomorphism reflection. -/
theorem isIso_restrict_of_split_cartesian {W Y E X : Scheme.{u}}
    {p : W ⟶ Y} {u : W ⟶ E} {f : Y ⟶ X} {q : E ⟶ X}
    (H : IsPullback p u f q) (s : X ⟶ E) (hs : s ≫ q = 𝟙 X)
    (U : X.Opens) [IsIso (u ∣_ q ⁻¹ᵁ U)] : IsIso (f ∣_ U) := by
  have he : p ⁻¹ᵁ (f ⁻¹ᵁ U) = u ⁻¹ᵁ (q ⁻¹ᵁ U) :=
    congrArg (fun g => g ⁻¹ᵁ U) H.w
  have hr := Scheme.Hom.isPullback_resLE H (US := U) (UT := q ⁻¹ᵁ U)
    (UX := f ⁻¹ᵁ U) (UY := u ⁻¹ᵁ (q ⁻¹ᵁ U)) le_rfl le_rfl (by rw [he,inf_idem])
  have hsU : U ≤ s ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    intro x hx
    change q (s x) ∈ U
    exact (congrArg (fun g => g x) hs).symm ▸ hx
  let sU := s.resLE (q ⁻¹ᵁ U) U hsU
  have hsUq : sU ≫ (q ∣_ U) = 𝟙 U.toScheme := by
    dsimp only [sU]
    rw [← cancel_mono U.ι,Category.assoc,morphismRestrict_ι,← Category.assoc,
      Scheme.Hom.resLE_comp_ι,Category.assoc,hs,Category.comp_id,Category.id_comp]
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hr
  exact isIso_of_split_cartesian hr sU hsUq

/-- Native final cartesianness transported along literal SAME-history descent. -/
theorem lastStage_isPullback_of_eq {X Y : Scheme.{u}} (S : X.BlowUpSequence)
    (q : Y ⟶ X) [Flat q] (T : Y.BlowUpSequence) (h : T = S.pullback q) :
    IsPullback (eqToHom (congrArg Scheme.BlowUpSequence.last h) ≫ S.pullbackLastHom q)
      T.composite S.composite q := by
  subst h
  simpa only [eqToHom_refl,Category.id_comp] using ActualFinalClopenProductPresentation.lastStage_isPullback S q

open ActualDimensionGroupBlowup ActualDimensionGroupRegularLocus ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualPaddedNativePrincipalizationInput ActualOriginalSingPrincipalizationHistoryDescent
  ActualPrincipalizedEndpointGeometry

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

private abbrev originalStructure : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

private instance originalStructure_finiteType : LocallyOfFiniteType (originalStructure R k) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

private theorem paddedOriginalRegular_le_smoothLocus :
    (envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ
      (originalStructure R k).smoothLocus ≤ ((paddedEnvelope R k).obj.hom).smoothLocus := by
  let U := (originalStructure R k).smoothLocus
  let g := envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R)
  let V := g ⁻¹ᵁ U
  have : Smooth (envelopeProjection R k) := envelopeProjection_smooth R k
  have : IsIso (affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U) :=
    separation_isIso_over_smoothLocus R k
  have : Smooth (U.ι ≫ originalStructure R k) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,← Scheme.Hom.preimage_smoothLocus_eq]
    exact U.ι_preimage_self
  have hcomp : Smooth (g ∣_ U ≫ U.ι ≫ originalStructure R k) := by
    rw [show g ∣_ U = envelopeProjection R k ∣_
        (affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ U ≫
        affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U from morphismRestrict_comp _ _ _]
    infer_instance
  have : Smooth (V.ι ≫ (paddedEnvelope R k).obj.hom) := by
    have he : g ∣_ U ≫ U.ι ≫ originalStructure R k = V.ι ≫ (paddedEnvelope R k).obj.hom := by
      rw [← Category.assoc,morphismRestrict_ι]
      rfl
    exact he ▸ hcomp
  intro x hx
  exact ((paddedEnvelope R k).obj.hom.mem_smoothLocus_iff_exists_smooth).mpr ⟨V,hx,inferInstance⟩

/-- SAME descended native resolution is an isomorphism above the ENTIRE ORIGINAL regular locus. -/
theorem nativeBaseHistory_isIso_over_original_regular :
    IsIso ((nativeBaseHistory R k).composite ∣_
      (affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ (originalStructure R k).smoothLocus) := by
  have : Smooth (envelopeProjection R k) := envelopeProjection_smooth R k
  have : IsIso ((nativePaddedHistory R k).composite ∣_ ((paddedEnvelope R k).obj.hom).smoothLocus) :=
    (nativePaddedHistory_isStrongResolution R k).isIso_restrict_smoothLocus
  have : IsIso ((nativePaddedHistory R k).composite ∣_
      (envelopeProjection R k) ⁻¹ᵁ
        (affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ (originalStructure R k).smoothLocus) :=
    isIso_restrict_of_le _ (paddedOriginalRegular_le_smoothLocus R k)
  exact isIso_restrict_of_split_cartesian
    (lastStage_isPullback_of_eq (nativeBaseHistory R k) (envelopeProjection R k)
      (nativePaddedHistory R k) (nativePaddedHistory_canonical_history_descends R k))
    (envelopeZeroSection R k) (envelopeZeroSection_projection R k) _

private theorem paddedOriginalSing_support :
    ((paddedFinalOriginalSing R k).support : Set (nativePaddedHistory R k).last) =
      ((nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
        affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹' ((originalStructure R k).smoothLocus : Set _)ᶜ := by
  rw [paddedFinalOriginalSing,support_comap,Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus (originalStructure R k),
    Scheme.singularLocus_eq_compl_smoothLocus (originalStructure R k)]

/-- SAME descended ORIGINAL-singular BP is an isomorphism above the ENTIRE ORIGINAL regular locus. -/
theorem nativeBasePrincipalizationHistory_isIso_over_original_regular :
    IsIso ((nativeBasePrincipalizationHistory R k).composite ∣_
      ((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ
        (originalStructure R k).smoothLocus) := by
  have : Smooth (paddedFinalProjection R k) := paddedFinalProjection_smooth R k
  let T := nativeOriginalSingPrincipalizationTriple R k
  have : IsIso ((nativeOriginalSingPrincipalizationHistory R k).composite ∣_
      (T.I.support ⊔ T.E.singularLocus).compl) := BP_isIso_restrict T
  have hEmpty : T.E.singularLocus = ⊥ := by
    change (Scheme.DivisorFamily.empty (nativePaddedHistory R k).last).singularLocus = ⊥
    simp [Scheme.DivisorFamily.singularLocus,Scheme.DivisorFamily.empty]
  have hle : (paddedFinalProjection R k) ⁻¹ᵁ
      ((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ
        (originalStructure R k).smoothLocus ≤ (T.I.support ⊔ T.E.singularLocus).compl := by
    intro x hx
    rw [hEmpty,sup_bot_eq]
    change x ∉ ((paddedFinalOriginalSing R k).support : Set (nativePaddedHistory R k).last)
    rw [paddedOriginalSing_support R k]
    change ¬ (affineBlowUp.π (dimensionSeparationIdeal R)
      (envelopeProjection R k ((nativePaddedHistory R k).composite x))) ∈
      ((originalStructure R k).smoothLocus : Set _)ᶜ
    have he := congrArg (fun g => affineBlowUp.π (dimensionSeparationIdeal R) (g x))
      (paddedFinalProjection_over R k)
    simp only [Scheme.Hom.comp_apply] at he
    change affineBlowUp.π (dimensionSeparationIdeal R)
      ((nativeBaseHistory R k).composite (paddedFinalProjection R k x)) ∈
        (originalStructure R k).smoothLocus at hx
    exact fun h => h (he ▸ hx)
  have : IsIso ((nativeOriginalSingPrincipalizationHistory R k).composite ∣_
      (paddedFinalProjection R k) ⁻¹ᵁ
        ((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹ᵁ
          (originalStructure R k).smoothLocus) := isIso_restrict_of_le _ hle
  exact isIso_restrict_of_split_cartesian
    (lastStage_isPullback_of_eq (nativeBasePrincipalizationHistory R k) (paddedFinalProjection R k)
      (nativeOriginalSingPrincipalizationHistory R k) (nativePrincipalization_canonical_history_descends R k))
    (nativeFinalSection R k) (nativeFinalSection_projection R k) _
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualHistoryOriginalRegularIsomorphism
