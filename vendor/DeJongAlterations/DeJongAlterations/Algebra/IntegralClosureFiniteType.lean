import DeJongAlterations.Algebra.IntegralClosureFiniteTypeSeparable
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finiteness of normalization over an arbitrary field

Noether normalization reduces a finite-type domain to the actual polynomial-base
finiteness theorem. Its purely inseparable cover is constructed in the preceding
modules, so the ground field need not be perfect.

The scalar-tower arrangement follows the existing pure proof in
`Geometry/AffineCurveAlteration.lean`; its perfect-field normal-base argument
is replaced by the new arbitrary-field polynomial-base construction.
-/

noncomputable section

namespace DeJongAlterations.Algebra.IntegralClosureFiniteType

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped nonZeroDivisors

/-- Actual integral closures of finite-type domains in finite field extensions are finite,
over an arbitrary ground field. No normality or finiteness certificate is supplied. -/
theorem finite_of_isIntegralClosure_of_finiteType (k D K L C : Type u) [Field k]
    [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] [Field K] [Algebra D K]
    [IsFractionRing D K] [Field L] [Algebra K L] [Algebra D L] [IsScalarTower D K L]
    [FiniteDimensional K L] [CommRing C] [Algebra C L] [Algebra D C] [IsScalarTower D C L]
    [IsIntegralClosure C D L] : Module.Finite D C := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k D
  let A := MvPolynomial (Fin s) k
  let F := FractionRing A
  let : Algebra A D := g.toRingHom.toAlgebra
  let : Module.Finite A D := hfin
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hg
  let : Algebra A K := ((algebraMap D K).comp (algebraMap A D)).toAlgebra
  let : IsScalarTower A D K := IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    ((IsFractionRing.injective D K).comp hg)
  let : Algebra F K := FractionRing.liftAlgebra A K
  let : IsScalarTower A F K := FractionRing.isScalarTower_liftAlgebra A K
  let : FiniteDimensional F K := Module.Finite.of_isLocalization A D A⁰
  let : Algebra A L := ((algebraMap D L).comp (algebraMap A D)).toAlgebra
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K L := IsScalarTower.to₁₃₄ A D K L
  let : IsScalarTower A F L := IsScalarTower.to₁₂₄ A F K L
  let : FiniteDimensional F L := Module.Finite.trans K L
  let : Algebra A C := ((algebraMap D C).comp (algebraMap A D)).toAlgebra
  let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C L := IsScalarTower.to₁₃₄ A D C L
  let : Algebra.IsIntegral A D := Algebra.IsIntegral.of_finite A D
  let : IsIntegralClosure C A L := by
    refine ⟨IsIntegralClosure.algebraMap_injective C D L, fun {x} => ?_⟩
    rw [← IsIntegralClosure.isIntegral_iff (A := C) (R := D)]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩
  let : Module.Finite A (integralClosure A L) :=
    IntegralClosureFiniteTypeSeparable.finite_integralClosure_polynomial k (Fin s) L
  let e := IsIntegralClosure.equiv A C L (integralClosure A L)
  let : Module.Finite A C := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_restrictScalars_finite A D C

section IntegralClosure

variable (k D L : Type u) [Field k] [CommRing D] [IsDomain D] [Algebra k D]
  [Algebra.FiniteType k D] [Field L] [Algebra D L] [IsFractionRing D L]

include k

/-- The actual normalization of a finite-type domain over any field is a finite module.
The ambient field may be any fraction field of the original domain. -/
theorem finite_integralClosure : Module.Finite D (integralClosure D L) :=
  finite_of_isIntegralClosure_of_finiteType k D L L (integralClosure D L)

/-- The same actual normalized ring is Noetherian over any ground field. -/
theorem isNoetherianRing_integralClosure : IsNoetherianRing (integralClosure D L) := by
  let : Module.Finite D (integralClosure D L) := finite_integralClosure k D L
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  exact Algebra.FiniteType.isNoetherianRing D (integralClosure D L)

/-- The actual normalization remains finite type over the arbitrary coefficient field. -/
theorem finiteType_integralClosure [Algebra k L] [IsScalarTower k D L] :
    Algebra.FiniteType k (integralClosure D L) := by
  let : Module.Finite D (integralClosure D L) := finite_integralClosure k D L
  exact Algebra.FiniteType.trans (S := D) inferInstance inferInstance

end IntegralClosure

end DeJongAlterations.Algebra.IntegralClosureFiniteType
