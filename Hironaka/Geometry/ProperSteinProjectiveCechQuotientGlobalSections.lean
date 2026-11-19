import Hironaka.Geometry.ProperSteinProjectiveCechQuotientDiagram
import Hironaka.Geometry.ProperSteinProjectiveCechSheafSections
import Hironaka.Geometry.ProperSteinProjectiveCechTwistingPresentation

/-! # ENTIRE original quotient regular functions are the actual internally finite Čech H0 -/

universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))

/-- The actual ORIGINAL coordinate basic opens on the SAME actual quotient. -/
def polynomialQuotientCoordinateOpens (i : I) : (polynomialQuotientScheme J).Opens :=
  Proj.basicOpen (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
    (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (MvPolynomial.X i))

omit [LinearOrder I] [Fintype I] in
/-- EVERY original finite intersection is the SAME actual quotient coordinate-product open. -/
theorem polynomialQuotientActualSubsetOpen_eq (S : Finset I) :
    actualSchemeSubsetOpen (polynomialQuotientCoordinateOpens J) S = polynomialQuotientSubsetOpen J S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [actualSchemeSubsetOpen, polynomialQuotientSubsetOpen, polynomialCoordinateProduct]
  | @insert i S hi ih =>
    simpa [actualSchemeSubsetOpen, polynomialQuotientCoordinateOpens, polynomialQuotientSubsetOpen,
      polynomialCoordinateProduct, Finset.prod_insert hi, Proj.basicOpen_mul] using
      congrArg (fun V : (polynomialQuotientScheme J).Opens =>
        polynomialQuotientCoordinateOpens J i ⊓ V) ih

omit [LinearOrder I] [Fintype I] in
/-- The SAME original quotient coordinate opens really cover, by the original ambient irrelevant-ideal cover. -/
theorem polynomialQuotientCoordinateOpens_covers :
    iSup (polynomialQuotientCoordinateOpens J) = ⊤ := by
  have hcover : (⨆ i : I, Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates
  let q := GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule I K) J
  change (⨆ i : I, q ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) = ⊤
  rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]

/-- True original open equalities identify the SAME native unit-sheaf cover diagram with actual regular sections. -/
def polynomialQuotientActualCoverDiagramIso :
    actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit (polynomialQuotientScheme J).ringCatSheaf)
        (polynomialQuotientCoordinateOpens J) (polynomialQuotientProjConstants J ⊤) ≅
      polynomialQuotientProductDiagram J :=
  NatIso.ofComponents
    (fun S => (ModuleCat.restrictScalars (polynomialQuotientProjConstants J ⊤)).mapIso
      (actualSchemeModuleOpenIso (SheafOfModules.unit (polynomialQuotientScheme J).ringCatSheaf)
        (polynomialQuotientActualSubsetOpen_eq J S))) (by
      intro S T f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change (polynomialQuotientScheme J).presheaf.map _
          ((polynomialQuotientScheme J).presheaf.map _ s) =
        (polynomialQuotientScheme J).presheaf.map _
          ((polynomialQuotientScheme J).presheaf.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl)

/-- Genuine native sheaf gluing gives ENTIRE original quotient regular functions as SAME actual Čech H0. -/
def polynomialQuotientGlobalH0Iso :
    actualSchemeModuleBaseGlobalSections (SheafOfModules.unit (polynomialQuotientScheme J).ringCatSheaf)
        (polynomialQuotientProjConstants J ⊤) ≅
      (subsetCechComplex (polynomialQuotientProductDiagram J)).homology 0 :=
  actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit (polynomialQuotientScheme J).ringCatSheaf)
    (polynomialQuotientCoordinateOpens J) (polynomialQuotientProjConstants J ⊤)
    (polynomialQuotientCoordinateOpens_covers J) ≪≫
      HomologicalComplex.homologyMapIso
        ((actualSubsetCechFunctor (K := K) (I := I)).mapIso (polynomialQuotientActualCoverDiagramIso J)) 0

/-- ENTIRE ORIGINAL quotient global regular functions are internally finite over the SAME original Noetherian ring. -/
theorem polynomialQuotientGlobalSections_finite [IsNoetherianRing K] :
    Module.Finite K Γ(polynomialQuotientScheme J, ⊤) := by
  let := polynomialQuotientProductCech_homology_finite J 0
  exact Module.Finite.equiv (polynomialQuotientGlobalH0Iso J).toLinearEquiv.symm

end
end Hironaka.Geometry.ProperSteinProjectiveCech
