import Hironaka.Geometry.NodeCompletedLocalFiber
import Hironaka.Algebra.NodeGeometricCompletionCoefficients

/-!
# Actual complete etale coefficients for an original finite type flat scheme morphism

The finite separable extension is the ORIGINAL canonical residue extension of
its original stalk map. Completed flatness and all replacement-ring properties
are derived internally; no completed fibre model is used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalMap

open Algebra.CompletionRegularityBasics
open Algebra.NodeGeometricCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

attribute [local instance] originalAlgebra Algebra.CompletionFlatMap.completedAlgebra

local instance originalStalkMap_local :
    IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

variable [LocallyOfFiniteType f] [IsLocallyNoetherian S]
  [FiniteDimensional (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))]
  [Algebra.IsSeparable (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))]

/-- The actual finite etale coefficient ring for the completed original scheme stalk map. -/
abbrev CompletedStalkCoefficientRing :=
  letI := originalTarget_isNoetherianRing f x
  CompletedCoefficientRing (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The actual upper map into the completed ORIGINAL source stalk. -/
def completedStalkCoefficientMap :
    CompletedStalkCoefficientRing f x →+* X.completedLocalRing x := by
  let := originalTarget_isNoetherianRing f x
  exact (completedCoefficientMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)).toRingHom

/-- The actual upper coefficient action. -/
@[instance_reducible]
def upperCompletedStalkAlgebra :
    Algebra (CompletedStalkCoefficientRing f x) (X.completedLocalRing x) :=
  (completedStalkCoefficientMap f x).toAlgebra

/-- All replacement-ring properties are derived from the original scheme data. -/
theorem completedStalkCoefficientRing_properties :
    Module.Finite (S.completedLocalRing (f x)) (CompletedStalkCoefficientRing f x) ∧
      Module.Free (S.completedLocalRing (f x)) (CompletedStalkCoefficientRing f x) ∧
      Algebra.Etale (S.completedLocalRing (f x)) (CompletedStalkCoefficientRing f x) ∧
      IsLocalRing (CompletedStalkCoefficientRing f x) ∧
      IsNoetherianRing (CompletedStalkCoefficientRing f x) ∧
      IsAdicComplete (maximalIdeal (CompletedStalkCoefficientRing f x))
        (CompletedStalkCoefficientRing f x) :=
  by
    let := originalTarget_isNoetherianRing f x
    exact completedCoefficientRing_properties (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The actual finite etale factorization preserves the full completed coefficient map. -/
theorem completedStalkCoefficientMap_triangle :
    (completedStalkCoefficientMap f x).comp
      (algebraMap (S.completedLocalRing (f x)) (CompletedStalkCoefficientRing f x)) =
        completedMap f x :=
  by
    let := originalTarget_isNoetherianRing f x
    exact completedCoefficientMap_triangle (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The original scheme stalk coefficient triangle survives the entire construction. -/
theorem completedStalkCoefficientMap_original (a : S.presheaf.stalk (f x)) :
    completedStalkCoefficientMap f x
      (algebraMap (S.completedLocalRing (f x)) (CompletedStalkCoefficientRing f x)
        (S.toCompletedLocalRing (f x) a)) =
          X.toCompletedLocalRing x (f.stalkMap x a) :=
  by
    let := originalTarget_isNoetherianRing f x
    exact completedCoefficientMap_original (S.presheaf.stalk (f x)) (X.presheaf.stalk x) a

/-- Upper flatness is derived from the ORIGINAL geometric flatness hypothesis. -/
theorem upperCompletedStalkAlgebra_flat [Flat f] :
    letI := upperCompletedStalkAlgebra f x
    Module.Flat (CompletedStalkCoefficientRing f x) (X.completedLocalRing x) := by
  let := originalTarget_isNoetherianRing f x
  let := originalAlgebra_essFiniteType f x
  let := originalAlgebra_flat f x
  exact upperCompletedAlgebra_flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The actual upper local homomorphism, derived from the constructed Hensel lift. -/
theorem upperCompletedStalk_isLocalHom :
    letI := originalTarget_isNoetherianRing f x
    IsLocalHom (completedStalkCoefficientMap f x) := by
  let := originalTarget_isNoetherianRing f x
  exact completedCoefficientMap_local (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The actual upper residue map is an isomorphism of the actual residue fields. -/
def upperCompletedStalkResidueEquiv :
    letI := originalTarget_isNoetherianRing f x
    ResidueField (CompletedStalkCoefficientRing f x) ≃+*
      ResidueField (X.completedLocalRing x) := by
  let := originalTarget_isNoetherianRing f x
  exact completedCoefficientResidueEquiv (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The upper completed closed fibre has the original uncompleted quotient completion,
without supplying any fibre presentation. -/
def upperClosedFiberEquiv :
    letI := originalFiberLocalRing f x
    (X.completedLocalRing x ⧸ (maximalIdeal (CompletedStalkCoefficientRing f x)).map
      (completedStalkCoefficientMap f x)) ≃+*
        Completion (X.presheaf.stalk x ⧸ originalFiberIdeal f x) := by
  let := originalTarget_isNoetherianRing f x
  exact upperClosedFiberCompletionEquiv (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- Every original germ has its exact original quotient image after the entire construction. -/
theorem upperClosedFiberEquiv_coefficient (b : X.presheaf.stalk x) :
    letI := originalFiberLocalRing f x
    upperClosedFiberEquiv f x (Ideal.Quotient.mk _ (X.toCompletedLocalRing x b)) =
      algebraMap (X.presheaf.stalk x ⧸ originalFiberIdeal f x)
        (Completion (X.presheaf.stalk x ⧸ originalFiberIdeal f x))
          (Ideal.Quotient.mk (originalFiberIdeal f x) b) := by
  let := originalTarget_isNoetherianRing f x
  exact upperClosedFiberCompletionEquiv_coefficient
    (S.presheaf.stalk (f x)) (X.presheaf.stalk x) b

end Hironaka.Geometry.NodeCompletedLocalMap
