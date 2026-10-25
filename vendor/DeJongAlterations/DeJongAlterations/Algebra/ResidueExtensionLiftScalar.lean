import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Finiteness.Basic

/-! # Transport of specified finite separable extensions along actual field isomorphisms -/

noncomputable section

namespace DeJongAlterations.Algebra.ResidueExtensionLift

universe u

variable {K F L : Type u} [Field K] [Field F] [Field L] [Algebra F L]

/-- The actual composite scalar map through the given base-field isomorphism. -/
abbrev algebraOfEquiv (e : K ≃+* F) : Algebra K L :=
  ((algebraMap F L).comp e.toRingHom).toAlgebra

/-- Finiteness transports through the actual base-field isomorphism. -/
theorem finite_of_equiv (e : K ≃+* F) [FiniteDimensional F L] :
    letI := algebraOfEquiv (L := L) e
    FiniteDimensional K L := by
  let := algebraOfEquiv (L := L) e
  let : Algebra K F := e.toRingHom.toAlgebra
  let : Module.Finite K F := Module.Finite.of_surjective (Algebra.linearMap K F) e.surjective
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.trans F L

/-- Actual separability transports through that same actual coefficient map. -/
theorem separable_of_equiv (e : K ≃+* F) [Algebra.IsSeparable F L] :
    letI := algebraOfEquiv (L := L) e
    Algebra.IsSeparable K L := by
  let := algebraOfEquiv (L := L) e
  apply Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl L)
  ext a
  change algebraMap F L (e (e.symm a)) = algebraMap F L a
  rw [e.apply_symm_apply]

end DeJongAlterations.Algebra.ResidueExtensionLift
