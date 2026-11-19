import Hironaka.Geometry.ProperSteinProjectiveCechTwistingCoordinateNaturality
import Hironaka.Geometry.ProperSteinProjectiveCechNonemptyComparison

/-!
# Actual original twisting-sheaf coordinate diagrams have internally finite native cohomology

Native original sheaf restrictions and the SAME actual polynomial constants form
the diagram. The actual original nonempty coordinate comparisons are internally
produced; no desired diagram isomorphism or cohomology output is assumed.
-/

universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal ORIGINAL twisting restriction to an actual smaller coordinate-product basic open. -/
def polynomialTwistingProductRestriction (k : ℕ) {S T : Finset I} (hST : S ⊆ T) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)) →ₗ[K]
      bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct T)) where
  toFun := (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).val.map
    (homOfLE (Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST))).op
  map_add' s t := ((projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).val.map
    (homOfLE (Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST))).op).hom.map_add s t
  map_smul' r s := by
    change (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).val.map
      (homOfLE (Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST))).op
      (homogeneousPolynomialProjConstants
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)) r • s) =
        homogeneousPolynomialProjConstants
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct T)) r •
          (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).val.map
            (homOfLE (Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST))).op s
    rw [PresheafOfModules.map_smul]
    rfl

/-- The ORIGINAL twisting diagram consists of actual original sections and literal original restrictions. -/
def polynomialTwistingProductDiagram (k : ℕ) : Finset I ⥤ ModuleCat.{u} K where
  obj S := ModuleCat.of K
    (bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)))
  map h := ModuleCat.ofHom (polynomialTwistingProductRestriction k (leOfHom h))
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
    change (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _ s =
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _
        ((projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _ s)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

/-- Genuine original ALL-prime restriction identities produce the actual original nonempty diagram isomorphism. -/
def polynomialTwistingNonemptyCoordinateIso (k : ℕ) :
    nonemptySubsetDiagram (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (k : ℤ)) ≅
      nonemptySubsetDiagram (polynomialTwistingProductDiagram (K := K) (I := I) k) := by
  classical
  let e (S : {S : Finset I // S.Nonempty}) :=
    polynomialTwistingCoordinatePieceEquiv (K := K) k S.val S.property.choose S.property.choose_spec
  refine NatIso.ofComponents (fun S => (e S).symm.toModuleIso) ?_
  intro S T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (e T).injective
  have h := polynomialTwistingCoordinatePieceEquiv_restrict k (leOfHom f)
    S.property.choose T.property.choose S.property.choose_spec T.property.choose_spec ((e S).symm z)
  change (e T) ((e T).symm
      (homogeneousCoordinateSubsetRestriction (polynomialIntegralGrading (K := K) (I := I))
        (polynomialIntegralGrading (K := K) (I := I))
        (fun a => (MvPolynomial.X a : MvPolynomial I K)) polynomialCoordinate_X_degree
        (leOfHom f) (k : ℤ) z)) =
    (e T) ((projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).val.map
      (homOfLE (Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset (leOfHom f)))).op
      ((e S).symm z))
  rw [LinearEquiv.apply_symm_apply]
  simpa only [e, LinearEquiv.apply_symm_apply] using h

/-- The SAME original twisting-sheaf cover complex is actually the internally computed coordinate complex. -/
def polynomialTwistingCoordinateCechIso (k : ℕ) :
    subsetCechComplex (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (k : ℤ)) ≅
      subsetCechComplex (polynomialTwistingProductDiagram (K := K) (I := I) k) :=
  nonemptySubsetCechComplexIso (polynomialTwistingNonemptyCoordinateIso k)

/-- Native actual cover-Cech cohomology of EACH original nonnegative twisting sheaf is internally finite. -/
theorem polynomialTwistingProductCech_homology_finite [IsNoetherianRing K] (k : ℕ) (p : ℕ) :
    Module.Finite K ((subsetCechComplex (polynomialTwistingProductDiagram (K := K) (I := I) k)).homology p) := by
  let := polynomialCoordinateHomogeneousCech_homology_finite (K := K) (I := I) (k : ℤ) p
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso (polynomialTwistingCoordinateCechIso (K := K) (I := I) k) p).toLinearEquiv

end
end Hironaka.Geometry.ProperSteinProjectiveCech
