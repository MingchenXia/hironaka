import Hironaka.Resolution.Algebraic.ActualPaddedNativePrincipalizationInput
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial

/-!
# Actual terminal padded translations preserve ONE original-ideal principalization

Source-first proof:
`actual-padded-principalization-translation-equivariance-20261102.tex`.
All comparison identities are derived for actual maps and the SAME native clock.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualPaddedPrincipalizationTranslationEquivariance

noncomputable section

/-- The actual native terminal lift, transported only along the SAME whole-history identity. -/
def historyEndpointLift {X : Scheme.{u}} (S : X.BlowUpSequence)
    (a : X ⟶ X) (hS : S = S.pullback a) : S.last ⟶ S.last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last hS) ≫ S.pullbackLastHom a

/-- Actual cartesian stage geometry makes the native terminal lift an automorphism. -/
theorem historyEndpointLift_isIso {X : Scheme.{u}} (S : X.BlowUpSequence)
    (a : X ⟶ X) [IsIso a] (hS : S = S.pullback a) : IsIso (historyEndpointLift S a hS) := by
  have : IsIso (S.pullbackStageHom a (Fin.last _)) :=
    isIso_pullbackStageHom_of_isIso S a _
  have : IsIso (S.pullbackLastHom a) := by
    dsimp only [Scheme.BlowUpSequence.pullbackLastHom]
    infer_instance
  dsimp only [historyEndpointLift]
  infer_instance

/-- The actual terminal lift satisfies its genuine original projection square. -/
theorem historyEndpointLift_over {X : Scheme.{u}} (S : X.BlowUpSequence)
    (a : X ⟶ X) (hS : S = S.pullback a) :
    historyEndpointLift S a hS ≫ S.composite = S.composite ≫ a := by
  rw [historyEndpointLift, Category.assoc, pullbackLastHom_comp_composite, ← Category.assoc]
  exact congrArg (fun h => h ≫ a) (eqToHom_comp_composite_of_eq hS)

open ActualDimensionGroupBlowup ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualPaddedNativePrincipalizationInput

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- The actual lift of an original family of padded translations to the SAME native endpoint. -/
def paddedEndpointTranslation (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    (nativePaddedHistory R k).last ⟶ (nativePaddedHistory R k).last :=
  historyEndpointLift (nativePaddedHistory R k) (envelopeTranslation R k v)
    (nativePaddedHistory_eq_pullback_translation R k v)

/-- Every actual lifted original padded translation is an automorphism. -/
theorem paddedEndpointTranslation_isIso
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    IsIso (paddedEndpointTranslation R k v) :=
  historyEndpointLift_isIso (nativePaddedHistory R k) (envelopeTranslation R k v)
    (nativePaddedHistory_eq_pullback_translation R k v)

/-- The actual terminal translation fixes the actual composite to the ORIGINAL affine scheme. -/
theorem paddedEndpointTranslation_original_projection
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    paddedEndpointTranslation R k v ≫ ((nativePaddedHistory R k).composite ≫
      envelopeProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R)) =
        (nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
          affineBlowUp.π (dimensionSeparationIdeal R) := by
  rw [← Category.assoc]
  rw [show paddedEndpointTranslation R k v ≫ (nativePaddedHistory R k).composite =
      (nativePaddedHistory R k).composite ≫ envelopeTranslation R k v from
    historyEndpointLift_over _ _ _]
  rw [Category.assoc, ← Category.assoc (envelopeTranslation R k v),
    envelopeTranslation_projection]

/-- Actual geometry fixing the ORIGINAL projection derives literal WHOLE principalization equivariance. -/
theorem principalization_eq_pullback_of_original_projection
    (g : (nativePaddedHistory R k).last ⟶ (nativePaddedHistory R k).last) [IsIso g]
    (hg : g ≫ ((nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
        affineBlowUp.π (dimensionSeparationIdeal R)) =
      (nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
        affineBlowUp.π (dimensionSeparationIdeal R)) :
    nativeOriginalSingPrincipalizationHistory R k =
      (nativeOriginalSingPrincipalizationHistory R k).pullback g := by
  let T := nativeOriginalSingPrincipalizationTriple R k
  have hfield : g ≫ (T.X.left ↘ Spec (.of k)) = T.X.left ↘ Spec (.of k) := by
    change g ≫ ((nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
      affineBlowUp.π (dimensionSeparationIdeal R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) =
        (nativePaddedHistory R k).composite ≫ envelopeProjection R k ≫
          affineBlowUp.π (dimensionSeparationIdeal R) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k R))
    simpa only [Category.assoc] using
      (congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) hg)
  have hI : T.I = T.I.comap g := by
    change paddedFinalOriginalSing R k = (paddedFinalOriginalSing R k).comap g
    rw [paddedFinalOriginalSing, ← comap_comp, hg]
  have hE : T.E = T.E.comap g := by
    change Scheme.DivisorFamily.empty _ = (Scheme.DivisorFamily.empty _).comap g
    exact (empty_comap g).symm
  exact BP_pullback_of_surjective T T g (surjective_of_isIso g) ⟨hfield,hI,hE⟩

/-- The ONE native principalization retains its ENTIRE clock under actual padded translations. -/
theorem principalization_eq_pullback_translation
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    nativeOriginalSingPrincipalizationHistory R k =
      (nativeOriginalSingPrincipalizationHistory R k).pullback (paddedEndpointTranslation R k v) := by
  have : IsIso (paddedEndpointTranslation R k v) := paddedEndpointTranslation_isIso R k v
  exact principalization_eq_pullback_of_original_projection R k _
    (paddedEndpointTranslation_original_projection R k v)
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualPaddedPrincipalizationTranslationEquivariance
