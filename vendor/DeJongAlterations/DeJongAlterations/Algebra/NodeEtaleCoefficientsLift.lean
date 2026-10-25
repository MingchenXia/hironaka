import DeJongAlterations.Algebra.ResidueExtensionLiftPoint
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Flat

/-! # The actual finite-free residue lift over a local ring is local and étale everywhere -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeEtaleCoefficients

open IsLocalRing
open DeJongAlterations.Algebra.ResidueExtensionLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A : Type u) [CommRing A] [IsLocalRing A]
  (L : Type u) [Field L] [Algebra (maximalIdeal A).ResidueField L]
  [FiniteDimensional (maximalIdeal A).ResidueField L]
  [Algebra.IsSeparable (maximalIdeal A).ResidueField L]

/-- The literal monic root algebra supplied by the actual residue-extension construction. -/
abbrev Coefficients := LiftRing (maximalIdeal A) L

/-- Integral contraction and the actual single-point closed fibre give genuine locality. -/
instance coefficients_isLocalRing : IsLocalRing (Coefficients A L) := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨liftPrime (maximalIdeal A) L, inferInstance, ?_⟩
  intro Q hQ
  let : Q.IsMaximal := hQ
  have hc : Q.comap (algebraMap A (Coefficients A L)) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
  have he := unique_point_over (maximalIdeal A) L (⟨Q, inferInstance⟩)
    (PrimeSpectrum.ext hc)
  exact congrArg PrimeSpectrum.asIdeal he

/-- The original specialization kernel is exactly the actual maximal ideal. -/
theorem coefficients_maximalIdeal : maximalIdeal (Coefficients A L) = liftPrime (maximalIdeal A) L :=
  (IsLocalRing.eq_maximalIdeal (inferInstanceAs (liftPrime (maximalIdeal A) L).IsMaximal)).symm

instance coefficients_localHom : IsLocalHom (algebraMap A (Coefficients A L)) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap A (Coefficients A L))).out 4 0).mp
  rw [coefficients_maximalIdeal, liftPrime_comap]

/-- Separability forces the actual derivative to be a unit in the whole local algebra. -/
theorem coefficients_derivative_isUnit :
    IsUnit (derivativeElement (maximalIdeal A) L) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [coefficients_maximalIdeal]
  exact derivative_not_mem_liftPrime (maximalIdeal A) L

/-- The native derivative-open étale algebra is the entire actual coefficient algebra. -/
instance coefficients_etale : Algebra.Etale A (Coefficients A L) := by
  let d := derivativeElement (maximalIdeal A) L
  let : Algebra.Etale A (Localization.Away d) := derivativeLocalization_etale (maximalIdeal A) L
  exact Algebra.Etale.of_equiv
    ((IsLocalization.atUnit (Coefficients A L) (Localization.Away d) d
      (coefficients_derivative_isUnit A L)).restrictScalars A).symm

/-- The actual maximal ideal is the actual extension of the original base ideal. -/
theorem coefficients_map_maximalIdeal :
    (maximalIdeal A).map (algebraMap A (Coefficients A L)) = maximalIdeal (Coefficients A L) :=
  Algebra.FormallyUnramified.map_maximalIdeal

instance coefficients_noetherian [IsNoetherianRing A] : IsNoetherianRing (Coefficients A L) :=
  IsNoetherianRing.of_finite A (Coefficients A L)

end DeJongAlterations.Algebra.NodeEtaleCoefficients
