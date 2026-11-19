import Hironaka.Resolution.Algebraic.ActualGlobalPaddedSmoothComparison

/-!
# SAME original weak history and actual smooth-surjective endpoint square

Source-first proof: `actual-global-weak-resolution-smooth-surjective-20261102.tex`.
The actual first centre and independently proved SAME tail comparison
derive literal original-history equality and real cartesian endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalWeakResolutionSmoothSurjective

noncomputable section

theorem cons_eq_pullback_of_ideal_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (S : I.blowUp.BlowUpSequence)
    (T : J.blowUp.BlowUpSequence) (hJ : I.comap f = J)
    (hT : T = S.pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp hJ.symm) ≫
      Scheme.Hom.blowUpMap f I)) :
    Scheme.BlowUpSequence.cons Y J T = (Scheme.BlowUpSequence.cons X I S).pullback f := by
  subst J
  rw [pullback_cons]
  apply congrArg (Scheme.BlowUpSequence.cons Y (I.comap f))
  simpa only [eqToHom_refl, Category.id_comp] using hT

open ActualGlobalDimensionSeparationIdeal ActualGlobalDimensionClopenPartition
  ActualGlobalNativeHistoryDescent ActualGlobalOriginalRegularGeometry
  ActualGlobalSeparationSmoothNaturality ActualGlobalSeparationBlowupFunctoriality
  ActualGlobalPaddedSmoothComparison ActualHistoryOriginalRegularIsomorphism

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]

def weakHistory : X.BlowUpSequence := .cons X (separationIdeal X) (canonicalBaseHistory p)

theorem weakHistory_composite : (weakHistory p).composite =
    (canonicalBaseHistory p).composite ≫ separationProjection X := rfl

theorem weakHistory_smooth : Smooth ((weakHistory p).composite ≫ p) := by
  change Smooth (((canonicalBaseHistory p).composite ≫ separationProjection X) ≫ p)
  rw [Category.assoc]
  exact canonicalBaseHistory_smooth p

theorem weakHistory_isIso_original_regular : IsIso ((weakHistory p).composite ∣_ p.smoothLocus) := by
  have : IsIso (separationProjection X ∣_ p.smoothLocus) := separation_isIso_original_regular p
  have : IsIso ((canonicalBaseHistory p).composite ∣_ (separationProjection X) ⁻¹ᵁ p.smoothLocus) :=
    canonicalBaseHistory_isIso_original_regular p
  change IsIso (((canonicalBaseHistory p).composite ≫ separationProjection X) ∣_ p.smoothLocus)
  exact isIso_restrict_comp _ _ p.smoothLocus

variable {Y : Scheme.{u}} [IsNoetherian Y] [IsReduced Y]
    (f : Y ⟶ X) [Smooth f] [Surjective f] [IsSeparated (f ≫ p)]

theorem weakHistory_eq_pullback : weakHistory (f ≫ p) = (weakHistory p).pullback f :=
  cons_eq_pullback_of_ideal_eq f (separationIdeal X) (separationIdeal Y) (canonicalBaseHistory p)
    (canonicalBaseHistory (f ≫ p)) (separationIdeal_smooth p f) (baseHistory_smooth_surjective p f)

def endpointMap : (weakHistory (f ≫ p)).last ⟶ (weakHistory p).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (weakHistory_eq_pullback p f)) ≫
    (weakHistory p).pullbackLastHom f

theorem endpoint_isPullback : IsPullback (endpointMap p f) (weakHistory (f ≫ p)).composite
    (weakHistory p).composite f :=
  lastStage_isPullback_of_eq (weakHistory p) f (weakHistory (f ≫ p)) (weakHistory_eq_pullback p f)

theorem endpoint_over : endpointMap p f ≫ (weakHistory p).composite =
    (weakHistory (f ≫ p)).composite ≫ f := (endpoint_isPullback p f).w

theorem endpoint_smooth : Smooth (endpointMap p f) :=
  property_of_isPullback _ (endpoint_isPullback p f) (inferInstance : Smooth f)

theorem endpoint_surjective : Surjective (endpointMap p f) :=
  property_of_isPullback _ (endpoint_isPullback p f) (inferInstance : Surjective f)

end
end Hironaka.Resolution.Algebraic.ActualGlobalWeakResolutionSmoothSurjective
