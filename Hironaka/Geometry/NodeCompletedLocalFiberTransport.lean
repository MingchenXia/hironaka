import Hironaka.Geometry.NodeCompletedLocalFiberQuotient
import Hironaka.Geometry.NodeCompletedLocalCoefficients

/-! Actual completed closed fibres are the completed local rings of the ACTUAL original scheme fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  [LocallyOfFiniteType f] [IsLocallyNoetherian S]

/-- The completed original closed fibre is the completed local ring of the actual original
scheme fibre; both comparisons are constructed internally. -/
def closedFiberActualCompletedEquiv :
    (X.completedLocalRing x ⧸
      (maximalIdeal (S.completedLocalRing (f x))).map (completedMap f x)) ≃+*
        (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) :=
  (closedFiberCompletionEquiv f x).trans (originalFiberCompletedEquiv f x).symm

/-- Every original germ keeps its exact geometric image after passing to the actual fibre completion. -/
theorem closedFiberActualCompletedEquiv_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    closedFiberActualCompletedEquiv f x
      (Ideal.Quotient.mk _ (X.toCompletedLocalRing x (X.presheaf.germ U x hx a))) =
      (f.fiber (f x)).toCompletedLocalRing (originalFiberPoint f x)
        ((f.fiberι (f x)).stalkMap (originalFiberPoint f x)
          (X.presheaf.germ U (f.fiberι (f x) (originalFiberPoint f x))
            (by simpa only [originalFiberPoint_source] using hx) a)) := by
  apply (originalFiberCompletedEquiv f x).injective
  change originalFiberCompletedEquiv f x
    ((originalFiberCompletedEquiv f x).symm
      (closedFiberCompletionEquiv f x (Ideal.Quotient.mk _
        (X.toCompletedLocalRing x (X.presheaf.germ U x hx a))))) = _
  rw [RingEquiv.apply_symm_apply, closedFiberCompletionEquiv_coefficient,
    originalFiberCompletedEquiv_germ]
  rfl

attribute [local instance] originalAlgebra

local instance originalStalkMap_forUpper :
    IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

variable [FiniteDimensional (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))]
  [Algebra.IsSeparable (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))]

/-- The SAME actual upper coefficient map has the completed local ring of the ACTUAL original fibre. -/
def upperClosedFiberActualCompletedEquiv :
    (X.completedLocalRing x ⧸ (maximalIdeal (CompletedStalkCoefficientRing f x)).map
      (completedStalkCoefficientMap f x)) ≃+*
        (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) :=
  (upperClosedFiberEquiv f x).trans (originalFiberCompletedEquiv f x).symm

/-- The full upper comparison preserves every actual original local section germ. -/
theorem upperClosedFiberActualCompletedEquiv_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    upperClosedFiberActualCompletedEquiv f x
      (Ideal.Quotient.mk _ (X.toCompletedLocalRing x (X.presheaf.germ U x hx a))) =
      (f.fiber (f x)).toCompletedLocalRing (originalFiberPoint f x)
        ((f.fiberι (f x)).stalkMap (originalFiberPoint f x)
          (X.presheaf.germ U (f.fiberι (f x) (originalFiberPoint f x))
            (by simpa only [originalFiberPoint_source] using hx) a)) := by
  apply (originalFiberCompletedEquiv f x).injective
  change originalFiberCompletedEquiv f x
    ((originalFiberCompletedEquiv f x).symm
      (upperClosedFiberEquiv f x (Ideal.Quotient.mk _
        (X.toCompletedLocalRing x (X.presheaf.germ U x hx a))))) = _
  rw [RingEquiv.apply_symm_apply, upperClosedFiberEquiv_coefficient,
    originalFiberCompletedEquiv_germ]
  rfl

end Hironaka.Geometry.NodeCompletedLocalMap
