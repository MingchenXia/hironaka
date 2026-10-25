import DeJongAlterations.Algebra.NodeFittingRelativeComparison
import DeJongAlterations.Algebra.NodeSingularJacobian

/-! # The ENTIRE original relative Fitting ideal under the SAME actual normal form

The input is the original local algebra, its actual coefficient lift and actual
normal form. The original coherent-to-formal-gradient comparison is constructed
internally; no singular-ideal or differential-presentation certificate is an input.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingRelativeTrace

open NodeFittingModule NodeFittingFormalDerivation NodeFittingRelativeComparison
  NodeFittingCompletedEtaleCoefficients NodeGeometricCompletionCoherentDifferentials

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]
  [IsNoetherianRing R] [Algebra.EssFiniteType A R]

local notation "Â" => AdicCompletion (maximalIdeal A) A
local notation "C" => AdicCompletion (maximalIdeal R) R
local notation "P" => CompletedOmega A R (maximalIdeal R)

local instance : Algebra Â C := completedBaseAlgebra A R

/-- The intrinsic Fitting ideal of the SAME ORIGINAL relative differential module. -/
def originalFittingIdeal (i : ℕ) : Ideal R := by
  letI := originalOmega_finitePresentation A R
  exact fittingIdeal (R := R) (M := KaehlerDifferential A R) i

variable (S : Type u) [CommRing S] [IsLocalRing S]
  [Algebra (AdicCompletion (maximalIdeal A) A) S]
  [Algebra S (AdicCompletion (maximalIdeal R) R)]
  [IsScalarTower (AdicCompletion (maximalIdeal A) A) S
    (AdicCompletion (maximalIdeal R) R)]
  [Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A) S]

section General

variable (F : Series S) (e : AdicCompletion (maximalIdeal R) R ≃ₐ[S] Hypersurface F)

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- EVERY full original Fitting ideal follows the actual original completion map and SAME normal form. -/
theorem completedFittingIdeal_eq_model (i : ℕ) :
    (originalFittingIdeal A R i).map (e.toRingHom.comp (algebraMap R C)) =
      fittingIdeal (R := Hypersurface F) (M := GradientModule F) i := by
  let := originalOmega_finitePresentation A R
  let := completedOmega_finitePresentation A R (maximalIdeal R)
  have hC : (originalFittingIdeal A R i).map (algebraMap R C) =
      fittingIdeal (R := C) (M := P) i :=
    (fittingIdeal_baseChange (R := R) (M := KaehlerDifferential A R) C i).trans
      (fittingIdeal_equiv (completedOmegaTensorEquiv A R (maximalIdeal R)) i)
  rw [← Ideal.map_map, hC]
  exact fittingIdeal_semilinear e.toRingEquiv (completedGradientEquiv A R S F e) i

/-- The ENTIRE original first Fitting trace is the SAME actual formal partial-derivative ideal. -/
theorem originalFittingIdeal_eq_gradient :
    (originalFittingIdeal A R 1).map (e.toRingHom.comp (algebraMap R C)) =
      Ideal.span {quotientMap F (MvPowerSeries.pderiv S 0 F),
        quotientMap F (MvPowerSeries.pderiv S 1 F)} :=
  (completedFittingIdeal_eq_model A R S F e 1).trans
    (NodeFittingFormalUniversal.gradient_fittingIdeal F)

end General

section Quadratic

variable (Q : NodeNonsplit.Quadratic S) (h : S)
  (e : AdicCompletion (maximalIdeal R) R ≃ₐ[S] NodeSingular.Node Q h)

/-- Unit discriminant identifies the FULL ORIGINAL singular trace with both actual coordinate classes, including characteristic two. -/
theorem originalFittingIdeal_eq_coordinateIdeal :
    (originalFittingIdeal A R 1).map (e.toRingHom.comp (algebraMap R C)) =
      NodeSingular.coordinateIdeal Q h := by
  calc
    _ = Ideal.span
        {quotientMap (Q.series - MvPowerSeries.C h)
          (MvPowerSeries.pderiv S 0 (Q.series - MvPowerSeries.C h)),
         quotientMap (Q.series - MvPowerSeries.C h)
          (MvPowerSeries.pderiv S 1 (Q.series - MvPowerSeries.C h))} :=
      originalFittingIdeal_eq_gradient A R S (Q.series - MvPowerSeries.C h) e
    _ = NodeSingular.jacobianIdeal Q h := by
      unfold NodeSingular.jacobianIdeal
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      rfl
    _ = NodeSingular.coordinateIdeal Q h := NodeSingular.jacobianIdeal_eq_coordinateIdeal Q h

/-- The actual original completed singular quotient, with the SAME actual S coefficient map. -/
def originalSingularQuotientEquiv :
    (C ⧸ (originalFittingIdeal A R 1).map (algebraMap R C)) ≃ₐ[S]
      S ⧸ Ideal.span {h} :=
  (Ideal.quotientEquivAlg
    ((originalFittingIdeal A R 1).map (algebraMap R C))
    (NodeSingular.coordinateIdeal Q h) e (by
      rw [Ideal.map_map]
      exact (originalFittingIdeal_eq_coordinateIdeal A R S Q h e).symm)).trans
    ((Ideal.quotientEquivAlgOfEq S (NodeSingular.gradientIdeal_eq Q h).symm).trans
      (NodeSingular.gradientQuotientEquiv Q h))

/-- EVERY actual original completed representative follows its SAME e image and original parameter evaluation. -/
theorem originalSingularQuotientEquiv_mk (c : C) :
    originalSingularQuotientEquiv A R S Q h e
      (Ideal.Quotient.mk ((originalFittingIdeal A R 1).map (algebraMap R C)) c) =
      NodeSingular.nodeEvaluation Q h (e c) := rfl

/-- EVERY actual original S coefficient retains its native parameter-zero residue class. -/
theorem originalSingularQuotientEquiv_coefficient (s : S) :
    originalSingularQuotientEquiv A R S Q h e
      (Ideal.Quotient.mk ((originalFittingIdeal A R 1).map (algebraMap R C))
        (algebraMap S C s)) = Ideal.Quotient.mk (Ideal.span {h}) s :=
  (originalSingularQuotientEquiv A R S Q h e).commutes s

end Quadratic

end DeJongAlterations.Algebra.NodeFittingRelativeTrace
