import DeJongAlterations.Algebra.NodeFittingFormalUniversal
import DeJongAlterations.Algebra.NodeFittingFormalDensity
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Actual finite formal-local targets have native variable-adic Hausdorffness

The SAME original quotient map and the full variable-ideal image are used.
No coefficient/variable filtration identification or Hausdorff certificate input.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingFormalHausdorff

open NodeFittingFormalDerivation NodeFittingFormalDensity

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

section Restriction
variable (F : Series R) (M : Type u) [AddCommGroup M] [Module (Hypersurface F) M]

/-- The ENTIRE restricted module action is compatible with the SAME actual quotient ring action. -/
theorem quotient_module_tower :
    letI : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
    IsScalarTower (Series R) (Hypersurface F) M := by
  let : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
  refine ⟨fun r b m => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  change (algebraMap (Series R) (Hypersurface F) r *
      algebraMap (Series R) (Hypersurface F) s) • m =
    algebraMap (Series R) (Hypersurface F) r •
      (algebraMap (Series R) (Hypersurface F) s • m)
  exact mul_smul _ _ _

variable [Module R M] [IsScalarTower R (Hypersurface F) M]

/-- EVERY original coefficient action is compatible with the SAME actual restricted quotient action. -/
theorem quotient_base_tower :
    letI : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
    IsScalarTower R (Series R) M := by
  let : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
  refine ⟨fun r s m => ?_⟩
  change quotientMap F (r • s) • m = r • (quotientMap F s • m)
  rw [map_smul, smul_assoc]

end Restriction

variable [IsLocalRing R] (F : Series R) [IsLocalRing (Hypersurface F)]

/-- The WHOLE original variable ideal maps into the SAME native formal-local maximal ideal. -/
theorem map_variables_le_maximalIdeal :
    (variableIdeal R).map (algebraMap (Series R) (Hypersurface F)) ≤
      maximalIdeal (Hypersurface F) := by
  let : IsLocalHom (algebraMap (Series R) (Hypersurface F)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hx : MvPowerSeries.X i ∈ maximalIdeal (Series R) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hc := MvPowerSeries.isUnit_constantCoeff _ hu
    exact not_isUnit_zero (by simpa only [MvPowerSeries.constantCoeff_X] using hc)
  exact (map_maximalIdeal_le (algebraMap (Series R) (Hypersurface F)))
    (Ideal.mem_map_of_mem _ hx)

variable [IsNoetherianRing (Hypersurface F)]

/-- Native local Noetherian Krull intersection supplies the ACTUAL finite target's Hausdorffness internally. -/
theorem module_variableHausdorff (M : Type u) [AddCommGroup M] [Module (Hypersurface F) M]
    [Module.Finite (Hypersurface F) M] :
    letI : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
    IsHausdorff (variableIdeal R) M := by
  let : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
  let : IsScalarTower (Series R) (Hypersurface F) M := quotient_module_tower F M
  exact IsHausdorff.of_map (I := variableIdeal R) (J := maximalIdeal (Hypersurface F))
    (map_variables_le_maximalIdeal F)

section FiniteUniversal

variable {M : Type u} [AddCommGroup M] [Module (Hypersurface F) M] [Module R M]
  [IsScalarTower R (Hypersurface F) M] [Module.Finite (Hypersurface F) M]

/-- The concrete actual finite-target universal map constructs ALL original quotient actions internally. -/
def finiteUniversalLift (D : Derivation R (Hypersurface F) M) :
    GradientModule F →ₗ[Hypersurface F] M := by
  letI : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
  letI : IsScalarTower (Series R) (Hypersurface F) M := quotient_module_tower F M
  letI : IsScalarTower R (Series R) M := quotient_base_tower F M
  letI : IsHausdorff (variableIdeal R) M := module_variableHausdorff F M
  exact NodeFittingFormalUniversal.universalLift F D

/-- Full native factorization on EVERY actual formal quotient element, with no supplied Hausdorff certificate. -/
theorem finiteUniversalLift_comp (D : Derivation R (Hypersurface F) M) :
    (finiteUniversalLift F D).compDer (formalDerivation F) = D := by
  let : Module (Series R) M := Module.compHom M (algebraMap (Series R) (Hypersurface F))
  let : IsScalarTower (Series R) (Hypersurface F) M := quotient_module_tower F M
  let : IsScalarTower R (Series R) M := quotient_base_tower F M
  let : IsHausdorff (variableIdeal R) M := module_variableHausdorff F M
  exact NodeFittingFormalUniversal.universalLift_comp F D

/-- BOTH original coordinate values are retained in the native original target module. -/
theorem finiteUniversalLift_coordinate (D : Derivation R (Hypersurface F) M) (i : Fin 2) :
    finiteUniversalLift F D (coordinateClass F i) = D (quotientMap F (MvPowerSeries.X i)) := by
  have h := DFunLike.congr_fun (finiteUniversalLift_comp F D) (quotientMap F (MvPowerSeries.X i))
  change finiteUniversalLift F D (formalDerivation F (quotientMap F (MvPowerSeries.X i))) = _ at h
  rw [formalDerivation_coordinate] at h
  exact h

/-- Uniqueness for actual native linear maps to the original finite target. -/
theorem finiteUniversalLift_unique (D : Derivation R (Hypersurface F) M)
    (L : GradientModule F →ₗ[Hypersurface F] M) (hL : L.compDer (formalDerivation F) = D) :
    L = finiteUniversalLift F D := by
  apply NodeFittingFormalUniversal.gradientLinearMap_ext F
  intro i
  have h := DFunLike.congr_fun hL (quotientMap F (MvPowerSeries.X i))
  change L (formalDerivation F (quotientMap F (MvPowerSeries.X i))) = _ at h
  rw [formalDerivation_coordinate] at h
  exact h.trans (finiteUniversalLift_coordinate F D i).symm

/-- Unique existence with the actual quotient actions and Hausdorffness ENTIRELY internal. -/
theorem existsUnique_finite_factorization (D : Derivation R (Hypersurface F) M) :
    ∃! L : GradientModule F →ₗ[Hypersurface F] M, L.compDer (formalDerivation F) = D :=
  ⟨finiteUniversalLift F D, finiteUniversalLift_comp F D,
    fun L hL => finiteUniversalLift_unique F D L hL⟩

end FiniteUniversal

end DeJongAlterations.Algebra.NodeFittingFormalHausdorff
