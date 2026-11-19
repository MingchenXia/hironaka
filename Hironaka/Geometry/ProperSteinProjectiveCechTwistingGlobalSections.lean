import Hironaka.Geometry.ProperSteinProjectiveCechTwistingDiagram
import Hironaka.Geometry.ProperSteinProjectiveCechTwistingPresentation

/-!
# Entire original twisting global sections are internally finite over the original Noetherian base

The SAME original coordinate opens, finite intersections and native sheaf
restrictions are retained. Actual original sheaf gluing supplies H0, and
the internally produced original twisting-Cech comparison supplies finiteness.
No global-section, representation or desired Cech comparison output is assumed.
-/

universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ORIGINAL basic opens of the ORIGINAL polynomial coordinates. -/
def polynomialTwistingCoordinateOpens (i : I) : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)

omit [LinearOrder I] [Fintype I] in
/-- EACH original finite intersection is the SAME actual original product basic open. -/
theorem polynomialTwistingSubsetOpen_eq (S : Finset I) :
    actualSchemeSubsetOpen (polynomialTwistingCoordinateOpens (K := K) (I := I)) S =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [actualSchemeSubsetOpen, polynomialCoordinateProduct]
  | @insert i S hi ih =>
    simpa [actualSchemeSubsetOpen, polynomialTwistingCoordinateOpens, polynomialCoordinateProduct,
      Finset.prod_insert hi, Proj.basicOpen_mul] using
      congrArg (fun V : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens =>
        polynomialTwistingCoordinateOpens i ⊓ V) ih

omit [LinearOrder I] [Fintype I] in
/-- The ORIGINAL polynomial irrelevant ideal internally supplies the SAME original coordinate cover. -/
theorem polynomialTwistingCoordinateOpens_covers :
    iSup (polynomialTwistingCoordinateOpens (K := K) (I := I)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates

/-- Actual native restrictions along ORIGINAL open equalities give the SAME original section-diagram isomorphism. -/
def polynomialTwistingActualCoverDiagramIso (k : ℕ) :
    actualSchemeModuleBaseSubsetDiagram
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (polynomialTwistingCoordinateOpens (K := K) (I := I))
      (homogeneousPolynomialProjConstants (K := K) (I := I) ⊤) ≅
      polynomialTwistingProductDiagram (K := K) (I := I) k :=
  NatIso.ofComponents
    (fun S => (ModuleCat.restrictScalars (homogeneousPolynomialProjConstants (K := K) (I := I) ⊤)).mapIso
      (actualSchemeModuleOpenIso (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
        (polynomialTwistingSubsetOpen_eq S))) (by
      intro S T f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _
          ((projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _ s) =
        (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _
          ((projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl)

/-- Native ORIGINAL sheaf gluing identifies the entire original twisting global sections with SAME actual Cech H0. -/
def polynomialTwistingGlobalH0Iso (k : ℕ) :
    actualSchemeModuleBaseGlobalSections
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (homogeneousPolynomialProjConstants (K := K) (I := I) ⊤) ≅
        (subsetCechComplex (polynomialTwistingProductDiagram (K := K) (I := I) k)).homology 0 :=
  actualSchemeModuleBaseGlobalHomologyIso
    (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
    (polynomialTwistingCoordinateOpens (K := K) (I := I))
    (homogeneousPolynomialProjConstants (K := K) (I := I) ⊤)
    polynomialTwistingCoordinateOpens_covers ≪≫
      HomologicalComplex.homologyMapIso
        ((actualSubsetCechFunctor (K := K) (I := I)).mapIso (polynomialTwistingActualCoverDiagramIso k)) 0

/-- EACH ORIGINAL nonnegative twisting sheaf has internally finite ENTIRE actual global sections over ANY Noetherian base. -/
theorem polynomialTwistingGlobalSections_finite [IsNoetherianRing K] (k : ℕ) :
    Module.Finite K
      (bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤) := by
  let := polynomialTwistingProductCech_homology_finite (K := K) (I := I) k 0
  exact Module.Finite.equiv (polynomialTwistingGlobalH0Iso (K := K) (I := I) k).toLinearEquiv.symm

end
end Hironaka.Geometry.ProperSteinProjectiveCech
