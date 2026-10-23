import DeJongAlterations.Algebra.NodeEtaleCoefficientsHensel
import DeJongAlterations.Algebra.NodeEtaleCoefficientsCompleteness

/-!
# Actual complete local étale coefficients for de Jong §2.23

The literal coefficient algebra, the local map into the original complete ring,
and both residue/coefficient triangles are constructed from the original local
map and its actual finite separable canonical residue extension.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeEtaleCoefficients

open IsLocalRing
open DeJongAlterations.Algebra.ResidueExtensionLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

attribute [local instance] residueAlgebra idealResidueAlgebra

variable [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  [IsAdicComplete (maximalIdeal B) B]

/-- The actual canonical residue map of the constructed local homomorphism is onto. -/
theorem coefficientResidueMap_surjective :
    Function.Surjective (IsLocalRing.ResidueField.map (coefficientMap A B).toRingHom) := by
  intro y
  obtain ⟨x, hx⟩ := specialization_surjective (maximalIdeal A) (ResidueField B) y
  refine ⟨residue (CoefficientRing A B) x, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  have he := RingHom.congr_fun (coefficientMap_residue A B) x
  exact he.trans hx

/-- The actual field identification is exactly the native residue map of the actual lifted map. -/
def coefficientResidueEquiv : ResidueField (CoefficientRing A B) ≃+* ResidueField B :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (coefficientMap A B).toRingHom)
    ⟨RingHom.injective _, coefficientResidueMap_surjective A B⟩

@[simp]
theorem coefficientResidueEquiv_residue (x : CoefficientRing A B) :
    coefficientResidueEquiv A B (residue (CoefficientRing A B) x) =
      specialization (maximalIdeal A) (ResidueField B) x :=
  RingHom.congr_fun (coefficientMap_residue A B) x

/-- The original canonical residue-field extension is preserved by the actual coefficient construction. -/
theorem coefficientResidueEquiv_triangle :
    (coefficientResidueEquiv A B).toRingHom.comp
      (IsLocalRing.ResidueField.map (algebraMap A (CoefficientRing A B))) =
        IsLocalRing.ResidueField.map (algebraMap A B) := by
  change (IsLocalRing.ResidueField.map (coefficientMap A B).toRingHom).comp
    (IsLocalRing.ResidueField.map (algebraMap A (CoefficientRing A B))) = _
  rw [← IsLocalRing.ResidueField.map_comp]
  congr 1
  ext a
  exact (coefficientMap A B).commutes a

/-- The actual original coefficient triangle commutes as ring maps. -/
theorem coefficientMap_triangle :
    (coefficientMap A B).toRingHom.comp (algebraMap A (CoefficientRing A B)) = algebraMap A B :=
  RingHom.ext (coefficientMap A B).commutes

/-- The literal new coefficient action on the original B is provided by the constructed map. -/
abbrev coefficientTargetAlgebra : Algebra (CoefficientRing A B) B :=
  (coefficientMap A B).toAlgebra

/-- The original A action is retained under the actual new coefficients. -/
theorem coefficientTargetScalarTower :
    letI := coefficientTargetAlgebra A B
    IsScalarTower A (CoefficientRing A B) B := by
  let := coefficientTargetAlgebra A B
  exact IsScalarTower.of_algebraMap_eq' (coefficientMap_triangle A B).symm

omit [IsAdicComplete (maximalIdeal B) B] in
/-- All replacement-ring properties hold for the actual internally constructed algebra. -/
theorem coefficientRing_properties [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] :
    Module.Finite A (CoefficientRing A B) ∧ Module.Free A (CoefficientRing A B) ∧
      Algebra.Etale A (CoefficientRing A B) ∧ IsLocalRing (CoefficientRing A B) ∧
      IsNoetherianRing (CoefficientRing A B) ∧
      IsAdicComplete (maximalIdeal (CoefficientRing A B)) (CoefficientRing A B) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end DeJongAlterations.Algebra.NodeEtaleCoefficients
