import DeJongAlterations.Algebra.NodeEtaleCoefficientsLift
import DeJongAlterations.Algebra.ResidueExtensionLiftScalar
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Actual canonical residue coefficients for the original local algebra map -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeEtaleCoefficients

open IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The actual scalar map is the canonical residue map of the original local algebra map. -/
abbrev residueAlgebra : Algebra (ResidueField A) (ResidueField B) :=
  inferInstance

attribute [local instance] residueAlgebra

/-- The ideal residue field is compared to the literal local residue quotient by its actual map. -/
def idealResidueEquiv : (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

@[simp]
theorem idealResidueEquiv_coefficient (a : A) :
    idealResidueEquiv A (algebraMap A (maximalIdeal A).ResidueField a) = residue A a := by
  apply (idealResidueEquiv A).symm.injective
  rw [RingEquiv.symm_apply_apply]
  change algebraMap A (maximalIdeal A).ResidueField a =
    algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField (Ideal.Quotient.mk _ a)
  rfl

/-- This second scalar structure is determined by that same original residue map. -/
abbrev idealResidueAlgebra : Algebra (maximalIdeal A).ResidueField (ResidueField B) :=
  ResidueExtensionLift.algebraOfEquiv (L := ResidueField B) (idealResidueEquiv A)

attribute [local instance] idealResidueAlgebra

instance idealResidue_finite [FiniteDimensional (ResidueField A) (ResidueField B)] :
    FiniteDimensional (maximalIdeal A).ResidueField (ResidueField B) :=
  @ResidueExtensionLift.finite_of_equiv (maximalIdeal A).ResidueField (ResidueField A) (ResidueField B)
    _ _ _ (residueAlgebra A B) (idealResidueEquiv A) inferInstance

instance idealResidue_separable [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Algebra.IsSeparable (maximalIdeal A).ResidueField (ResidueField B) :=
  ResidueExtensionLift.separable_of_equiv (L := ResidueField B) (idealResidueEquiv A)

@[simp]
theorem idealResidueAlgebra_coefficient (a : A) :
    algebraMap (maximalIdeal A).ResidueField (ResidueField B)
      (algebraMap A (maximalIdeal A).ResidueField a) = residue B (algebraMap A B a) := by
  change algebraMap (ResidueField A) (ResidueField B)
    (idealResidueEquiv A (algebraMap A (maximalIdeal A).ResidueField a)) = _
  rw [idealResidueEquiv_coefficient]
  rfl

end DeJongAlterations.Algebra.NodeEtaleCoefficients
