import Hironaka.Geometry.ProperSteinProjectiveCechQuotientNaturality
import Hironaka.Geometry.ProperSteinProjectiveCechNonemptyComparison

/-! # Actual native regular-section quotient diagrams have internally finite original Čech cohomology -/

universe u
open CategoryTheory Opposite AlgebraicGeometry
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))

/-- Literal ORIGINAL regular-section restriction retains the SAME actual quotient coefficient action. -/
def polynomialQuotientProductRestriction {S T : Finset I} (hST : S ⊆ T) :
    Γ(polynomialQuotientScheme J, polynomialQuotientSubsetOpen J S) →ₗ[K]
      Γ(polynomialQuotientScheme J, polynomialQuotientSubsetOpen J T) where
  toFun := (polynomialQuotientScheme J).presheaf.map (homOfLE (polynomialQuotientSubsetOpen_mono J hST)).op
  map_add' s t := ((polynomialQuotientScheme J).presheaf.map
    (homOfLE (polynomialQuotientSubsetOpen_mono J hST)).op).hom.map_add s t
  map_smul' r s := by
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl

/-- The SAME original quotient's native regular sections and literal restrictions form the actual diagram. -/
def polynomialQuotientProductDiagram : Finset I ⥤ ModuleCat.{u} K where
  obj S := ModuleCat.of K Γ(polynomialQuotientScheme J, polynomialQuotientSubsetOpen J S)
  map h := ModuleCat.ofHom (polynomialQuotientProductRestriction J (leOfHom h))
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    rfl
  map_comp hST hTV := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (polynomialQuotientScheme J).presheaf.map _ s =
      (polynomialQuotientScheme J).presheaf.map _ ((polynomialQuotientScheme J).presheaf.map _ s)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

/-- Genuine EVERY-prime restriction identities internally produce the SAME actual nonempty diagram isomorphism. -/
def polynomialQuotientNonemptyCoordinateIso :
    nonemptySubsetDiagram
        (homogeneousCoordinateSubsetDiagram (polynomialIntegralGrading (K := K) (I := I))
          (polynomialQuotientIntegralPiece J) (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree 0) ≅
      nonemptySubsetDiagram (polynomialQuotientProductDiagram J) := by
  refine NatIso.ofComponents
    (fun S => (polynomialQuotientRegularPieceEquiv J S.val S.property).toModuleIso) ?_
  intro S T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (polynomialQuotientRegularPieceEquiv_restrict J (leOfHom f) S.property T.property z).symm

/-- The ENTIRE actual regular-section quotient Čech complex is the SAME actual degree-zero module-fraction complex. -/
def polynomialQuotientCoordinateCechIso :
    homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
        (polynomialQuotientIntegralPiece J) (fun i => (MvPolynomial.X i : MvPolynomial I K))
        polynomialCoordinate_X_degree 0 ≅
      subsetCechComplex (polynomialQuotientProductDiagram J) :=
  nonemptySubsetCechComplexIso (polynomialQuotientNonemptyCoordinateIso J)

/-- Native actual regular-section coordinate-cover cohomology is internally finite in EVERY original degree. -/
theorem polynomialQuotientProductCech_homology_finite [IsNoetherianRing K] (p : ℕ) :
    Module.Finite K ((subsetCechComplex (polynomialQuotientProductDiagram J)).homology p) := by
  let := polynomialQuotientCoordinateCech_homology_finite J 0 p
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso (polynomialQuotientCoordinateCechIso J) p).toLinearEquiv

end
end Hironaka.Geometry.ProperSteinProjectiveCech
