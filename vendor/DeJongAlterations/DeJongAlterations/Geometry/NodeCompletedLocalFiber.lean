import DeJongAlterations.Geometry.NodeCompletedLocalMap

/-! Exact canonical closed-fibre and residue triangles of an original scheme morphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalMap

open Algebra.CompletionLocalMap Algebra.CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The original closed-fibre ideal in the actual original scheme stalk. -/
def originalFiberIdeal : Ideal (X.presheaf.stalk x) :=
  closedFiberIdeal (f.stalkMap x).hom

/-- The original closed-fibre quotient receives its actual local-ring structure internally. -/
theorem originalFiberLocalRing :
    IsLocalRing (X.presheaf.stalk x ⧸ originalFiberIdeal f x) :=
  Algebra.CompletionIdealQuotient.quotientLocalRing _
    (closedFiberIdeal_le_maximalIdeal (f.stalkMap x).hom)

variable [LocallyOfFiniteType f] [IsLocallyNoetherian S]

/-- The actual closed fibre of the literal completed map is the literal completion
of the actual original stalk closed-fibre quotient. -/
def closedFiberCompletionEquiv :
    letI := originalFiberLocalRing f x
    (X.completedLocalRing x ⧸
      (maximalIdeal (S.completedLocalRing (f x))).map (completedMap f x)) ≃+*
        Completion (X.presheaf.stalk x ⧸ originalFiberIdeal f x) := by
  let := originalTarget_isNoetherianRing f x
  exact closedFiberEquiv (f.stalkMap x).hom

/-- The completed closed-fibre comparison retains the image of every actual original germ. -/
theorem closedFiberCompletionEquiv_coefficient (b : X.presheaf.stalk x) :
    letI := originalFiberLocalRing f x
    closedFiberCompletionEquiv f x
      (Ideal.Quotient.mk _ (X.toCompletedLocalRing x b)) =
        algebraMap (X.presheaf.stalk x ⧸ originalFiberIdeal f x)
          (Completion (X.presheaf.stalk x ⧸ originalFiberIdeal f x))
          (Ideal.Quotient.mk (originalFiberIdeal f x) b) := by
  let := originalTarget_isNoetherianRing f x
  exact closedFiberEquiv_coefficient (f.stalkMap x).hom b

/-- The completed residue map retains exactly the original point residue map,
through the actual canonical completion residue maps on both sides. -/
theorem completedResidueMap_triangle :
    letI := originalTarget_isNoetherianRing f x
    letI := completedMap_isLocalHom f x
    (ResidueField.map (completedMap f x)).comp
      (ResidueField.map (algebraMap (S.presheaf.stalk (f x)) (S.completedLocalRing (f x)))) =
        (ResidueField.map (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))).comp (ResidueField.map (f.stalkMap x).hom) := by
  let := originalTarget_isNoetherianRing f x
  let := completedMap_isLocalHom f x
  rw [← ResidueField.map_comp, ← ResidueField.map_comp]
  congr 1

end DeJongAlterations.Geometry.NodeCompletedLocalMap
