import Hironaka.Algebra.NodeFittingExternalBaseStalk
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # The original native stalk map from the actual coefficient-valued stalk -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.RelativeUnramified

universe u

/-- The SAME canonical external coefficient equivalence makes the actual structural stalk map unramified. -/
theorem stalkMap_formallyUnramified_of_coefficientEquiv (K : Type u) [CommRing K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) (y : Y)
    (e : letI := Scheme.stalkAlgebra p y
      (Y.presheaf.stalk y) ≃ₐ[K] K) :
    (p.stalkMap y).hom.FormallyUnramified := by
  let := Scheme.stalkAlgebra (𝟙 (Spec (.of K))) (p y)
  let := Algebra.NodeFittingOmegaStalk.stalkAlgebra p y
  let := Scheme.stalkAlgebra p y
  let := Algebra.NodeFittingExternalBaseStalk.nativeBaseStalk_tower K p y
  let : Algebra.FormallyUnramified K (Y.presheaf.stalk y) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact Algebra.FormallyUnramified.of_restrictScalars K
    ((Spec (.of K)).presheaf.stalk (p y)) (Y.presheaf.stalk y)

end Hironaka.Geometry.RelativeUnramified
