import Hironaka.Geometry.ProperSteinProjectiveCechClosedSource
import Hironaka.Geometry.ProperSteinProjectiveCechSchemeIso

/-! # Every actual original projective coordinate-cover Cech cohomology module is finite -/
universe u
open CategoryTheory AlgebraicGeometry
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [CommRing K] {n : ℕ} {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace K n) [hi : IsClosedImmersion i]

/-- The SAME actual whole original quotient pullback retains the ENTIRE original coefficient homomorphism. -/
theorem originalClosedPullbackConstants :
    (originalClosedQuotientIso i).hom.appTop.hom.comp
      (polynomialQuotientProjConstants (originalClosedLiftedIdeal i) ⊤) = originalClosedConstants i := by
  let := (originalClosedConstants i).toAlgebra
  ext r
  exact (originalClosedGlobalSectionsEquiv i).commutes r

/-- Actual original coordinate opens, expressed by the SAME whole quotient isomorphism. -/
def originalClosedCoordinateOpens (j : ULift.{u} (Fin (n+1))) : X.Opens :=
  (originalClosedQuotientIso i).hom ⁻¹ᵁ polynomialQuotientCoordinateOpens (originalClosedLiftedIdeal i) j

/-- EACH actual coordinate open is EXACTLY the SAME original ambient-coordinate inverse image. -/
theorem originalClosedCoordinateOpens_eq (j : ULift.{u} (Fin (n+1))) :
    originalClosedCoordinateOpens i j =
      i ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K)
        (MvPolynomial.X j.down) := by
  let J := originalClosedQuotientIdeal i
  let q := GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K) J
  let E := polynomialQuotientReindexIso Equiv.ulift.symm J
  have hq : q ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K)
      (MvPolynomial.X j.down) =
      Proj.basicOpen (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K) J.toIdeal)
        (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j.down)) := rfl
  have hE : E.inv ⁻¹ᵁ
      Proj.basicOpen (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K) J.toIdeal)
        (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j.down)) =
      polynomialQuotientCoordinateOpens (originalClosedLiftedIdeal i) j := by
    change Proj.basicOpen _
      (Ideal.Quotient.mk _ (MvPolynomial.rename Equiv.ulift.symm (MvPolynomial.X j.down))) = _
    rw [MvPolynomial.rename_X]
    cases j
    rfl
  have h := originalClosedQuotientIso_hom_inclusion i
  change (originalClosedQuotientIso i).hom ≫ E.inv ≫ q = i at h
  conv_rhs => rw [← h, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hq, hE]
  rfl

/-- The SAME original finite coordinate family really covers the ORIGINAL source. -/
theorem originalClosedCoordinateOpens_covers : iSup (originalClosedCoordinateOpens i) = ⊤ := by
  change (⨆ j, (originalClosedQuotientIso i).hom ⁻¹ᵁ
    polynomialQuotientCoordinateOpens (originalClosedLiftedIdeal i) j) = ⊤
  rw [← Scheme.Hom.preimage_iSup, polynomialQuotientCoordinateOpens_covers, Scheme.Hom.preimage_top]

/-- Native positive-degree coordinate affinity and the ORIGINAL closed immersion give original affine opens. -/
theorem originalClosedCoordinateOpens_isAffine (j : ULift.{u} (Fin (n+1))) :
    IsAffineOpen (originalClosedCoordinateOpens i j) := by
  rw [originalClosedCoordinateOpens_eq]
  exact (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K)
    (MvPolynomial.X j.down) (MvPolynomial.isHomogeneous_X K j.down) (by decide : 0 < (1 : ℕ))).preimage i

/-- EVERY original regular-section restriction and coefficient gives the ENTIRE actual original Cech isomorphism. -/
def originalClosedRegularCechIso :
    subsetCechComplex
      (actualSchemeModuleBaseSubsetDiagram
        (SheafOfModules.unit (polynomialQuotientScheme (originalClosedLiftedIdeal i)).ringCatSheaf)
        (polynomialQuotientCoordinateOpens (originalClosedLiftedIdeal i))
        (polynomialQuotientProjConstants (originalClosedLiftedIdeal i) ⊤)) ≅
      subsetCechComplex
        (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf)
          (originalClosedCoordinateOpens i) (originalClosedConstants i)) := by
  unfold originalClosedCoordinateOpens
  simpa only [actualSchemePushforwardSourceConstants,
    originalClosedPullbackConstants] using
    actualSchemeIsoRegularCechIso (originalClosedQuotientIso i)
      (polynomialQuotientProjConstants (originalClosedLiftedIdeal i) ⊤)
      (polynomialQuotientCoordinateOpens (originalClosedLiftedIdeal i))

include hi in
/-- Genuine quotient finite-graded/Laurent cohomology and the ENTIRE original complex iso produce finiteness in EVERY actual original degree. -/
theorem originalClosedCoordinateCech_finite [IsNoetherianRing K] (p : ℕ) :
    Module.Finite K
      ((subsetCechComplex
        (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf)
          (originalClosedCoordinateOpens i) (originalClosedConstants i))).homology p) := by
  let J := originalClosedLiftedIdeal i
  let : Module.Finite K ((subsetCechComplex (polynomialQuotientProductDiagram J)).homology p) :=
    polynomialQuotientProductCech_homology_finite J p
  let E : subsetCechComplex
      (actualSchemeModuleBaseSubsetDiagram
        (SheafOfModules.unit (polynomialQuotientScheme J).ringCatSheaf)
        (polynomialQuotientCoordinateOpens J) (polynomialQuotientProjConstants J ⊤)) ≅
      subsetCechComplex (polynomialQuotientProductDiagram J) :=
    (actualSubsetCechFunctor (K := K) (I := ULift.{u} (Fin (n+1)))).mapIso
      (polynomialQuotientActualCoverDiagramIso J)
  let : Module.Finite K ((subsetCechComplex
      (actualSchemeModuleBaseSubsetDiagram
        (SheafOfModules.unit (polynomialQuotientScheme J).ringCatSheaf)
        (polynomialQuotientCoordinateOpens J) (polynomialQuotientProjConstants J ⊤))).homology p) :=
    Module.Finite.equiv (HomologicalComplex.homologyMapIso E p).toLinearEquiv.symm
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (originalClosedRegularCechIso i) p).toLinearEquiv

include hi in
/-- The SAME original native projective coefficient action gives finite ENTIRE actual coordinate Cech cohomology. -/
theorem originalClosedCoordinateCech_finite_original [IsNoetherianRing K] (p : ℕ) :
    Module.Finite K
      ((subsetCechComplex
        (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf)
          (originalClosedCoordinateOpens i)
          (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure K n)))).homology p) := by
  rw [← originalClosedConstants_eq_coefficientMap i]
  exact originalClosedCoordinateCech_finite i p

end
end Hironaka.Geometry.ProperSteinProjectiveCech
