import Hironaka.Algebra.NodeEtaleCoefficients
import Mathlib.RingTheory.Unramified.Finite

/-!
# Flatness for the same actual étale coefficient extension

Only original base flatness is assumed. The native unramified flatness theorem
constructs its actual tensor retraction internally; the coefficient action is
exactly the already constructed Hensel map, with the original scalar tower.
-/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleFlat

open IsLocalRing
open Hironaka.Algebra.NodeEtaleCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

attribute [local instance] NodeEtaleCoefficients.residueAlgebra NodeEtaleCoefficients.idealResidueAlgebra

variable [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  [IsAdicComplete (maximalIdeal B) B]

/-- Original base flatness implies genuine flatness over the same actual coefficient algebra. -/
theorem coefficientTarget_flat [Module.Flat A B] :
    letI := coefficientTargetAlgebra A B
    Module.Flat (CoefficientRing A B) B := by
  let := coefficientTargetAlgebra A B
  let := coefficientTargetScalarTower A B
  exact Algebra.FormallyUnramified.flat_of_restrictScalars
    (R := A) (S := CoefficientRing A B) B

/-- The actual upper maximal ideal has exactly the original image ideal in B. -/
theorem coefficientTarget_maximalIdeal_image :
    letI := coefficientTargetAlgebra A B
    (maximalIdeal (CoefficientRing A B)).map (algebraMap (CoefficientRing A B) B) =
      (maximalIdeal A).map (algebraMap A B) := by
  let := coefficientTargetAlgebra A B
  rw [← coefficients_map_maximalIdeal A (ResidueField B), Ideal.map_map]
  exact congrArg (fun f : A →+* B => (maximalIdeal A).map f) (coefficientMap_triangle A B)

end Hironaka.Algebra.NodeEtaleFlat
