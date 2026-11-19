import Hironaka.Geometry.ProperSteinProjectiveCechQuotientGlobalSections
import Hironaka.Geometry.ProperSteinProjectiveCechQuotientReindex
import Hironaka.Geometry.ProperSteinProjectiveCechGradedCoefficients
import Hironaka.Geometry.ProperSteinProjectiveCechStructureCoefficients
import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange
import Hironaka.Geometry.ProjectiveIdealRepresentation

/-! # The SAME original closed source, WHOLE kernel quotient and original finite functions -/

universe u
open CategoryTheory AlgebraicGeometry
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K : Type u} [CommRing K] {n : ℕ} {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (i : X ⟶ projectiveSpace K n) [hi : IsClosedImmersion i]

/-- The ORIGINAL actual closed immersion's WHOLE kernel internally constructs its genuine homogeneous ideal. -/
def originalClosedQuotientIdeal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) :=
  nativeHomogeneousRepresentative i.ker

/-- Native equality of WHOLE kernel sheaves identifies the SAME original source, before coordinate transport. -/
def originalClosedNativeQuotientIso :
    X ≅ Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (originalClosedQuotientIdeal i).toIdeal) := by
  let q := GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (originalClosedQuotientIdeal i)
  have h : q.ker = i.ker := nativeHomogeneousRepresentative_quotientIdealSheaf i.ker
  let : IsIso (IsClosedImmersion.lift q i h.le) := IsClosedImmersion.isIso_lift q i h
  exact asIso (IsClosedImmersion.lift q i h.le)

@[reassoc]
theorem originalClosedNativeQuotientIso_hom_inclusion :
    (originalClosedNativeQuotientIso i).hom ≫
      GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (originalClosedQuotientIdeal i) = i :=
  IsClosedImmersion.lift_fac _ _ _

/-- Actual finite coordinate lifting maps the SAME ENTIRE original homogeneous ideal. -/
def originalClosedLiftedIdeal :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) K) :=
  (originalClosedQuotientIdeal i).map (polynomialRenameGraded Equiv.ulift.symm)

/-- The SAME original source has its actual quotient in the original coefficient universe. -/
def originalClosedQuotientIso : X ≅ polynomialQuotientScheme (originalClosedLiftedIdeal i) :=
  (originalClosedNativeQuotientIso i).trans
    (polynomialQuotientReindexIso Equiv.ulift.symm (originalClosedQuotientIdeal i))

@[reassoc]
theorem originalClosedQuotientIso_hom_inclusion :
    (originalClosedQuotientIso i).hom ≫
      (polynomialQuotientReindexIso Equiv.ulift.symm (originalClosedQuotientIdeal i)).inv ≫
        GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
          (originalClosedQuotientIdeal i) = i := by
  simp only [originalClosedQuotientIso, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, originalClosedNativeQuotientIso_hom_inclusion]

/-- The SAME original coefficient action is pulled back along the ORIGINAL closed immersion. -/
def originalClosedConstants : K →+* Γ(X, ⊤) :=
  i.appTop.hom.comp (gradedProjectiveConstants (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ⊤)

omit [IsClosedImmersion i] in
/-- Actual coordinate rename retains EVERY ORIGINAL coefficient of the WHOLE original quotient. -/
theorem originalClosedReindexConstants (r : K) :
    (polynomialQuotientReindexIso Equiv.ulift.symm (originalClosedQuotientIdeal i)).hom.appTop
      (polynomialQuotientProjConstants (originalClosedLiftedIdeal i) ⊤ r) =
      gradedProjectiveConstants
        (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
          (originalClosedQuotientIdeal i).toIdeal) ⊤ r := by
  rw [← gradedProjectiveConstants_quotient]
  exact gradedProjectiveConstants_map _ _
    (polynomialRenameQuotientInverseGraded Equiv.ulift.symm (originalClosedQuotientIdeal i)) _
    (polynomialRenameQuotientEquiv Equiv.ulift.symm (originalClosedQuotientIdeal i)).symm.commutes ⊤ r

/-- The actual WHOLE original global-section equivalence retains the SAME original coefficient pullback. -/
def originalClosedGlobalSectionsEquiv :
    letI := (originalClosedConstants i).toAlgebra
    Γ(polynomialQuotientScheme (originalClosedLiftedIdeal i), ⊤) ≃ₐ[K] Γ(X, ⊤) := by
  let := (originalClosedConstants i).toAlgebra
  let e := (Scheme.Γ.mapIso (originalClosedQuotientIso i).op).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro r
  change (originalClosedNativeQuotientIso i).hom.appTop
    ((polynomialQuotientReindexIso Equiv.ulift.symm (originalClosedQuotientIdeal i)).hom.appTop
      (polynomialQuotientProjConstants (originalClosedLiftedIdeal i) ⊤ r)) =
      i.appTop (gradedProjectiveConstants (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ⊤ r)
  rw [originalClosedReindexConstants]
  have hq := gradedProjectiveConstants_map
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (originalClosedQuotientIdeal i).toIdeal)
    (GradedQuotient.gradedMk _ (originalClosedQuotientIdeal i).toIdeal)
    (GradedQuotient.irrelevant_le_map _ (originalClosedQuotientIdeal i)) (fun _ => rfl) ⊤ r
  have hq' :
      (GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (originalClosedQuotientIdeal i)).appTop
          (gradedProjectiveConstants (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ⊤ r) =
        gradedProjectiveConstants
          (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
            (originalClosedQuotientIdeal i).toIdeal) ⊤ r := hq
  have h := congrArg Scheme.Hom.appTop (originalClosedNativeQuotientIso_hom_inclusion i)
  rw [Scheme.Hom.comp_appTop] at h
  exact (congrArg (fun s => (originalClosedNativeQuotientIso i).hom.appTop s) hq'.symm).trans
    (ConcreteCategory.congr_hom h
      (gradedProjectiveConstants (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ⊤ r))

/-- The ENTIRE forward map is literally the ORIGINAL scheme isomorphism's actual pullback. -/
theorem originalClosedGlobalSectionsEquiv_apply
    (s : Γ(polynomialQuotientScheme (originalClosedLiftedIdeal i), ⊤)) :
    originalClosedGlobalSectionsEquiv i s = (originalClosedQuotientIso i).hom.appTop s := rfl

include hi in
/-- Actual quotient Čech finiteness gives finite ENTIRE ORIGINAL functions with the SAME original coefficients. -/
theorem originalClosedGlobalSections_finite [IsNoetherianRing K] :
    letI := (originalClosedConstants i).toAlgebra
    Module.Finite K Γ(X, ⊤) := by
  let := (originalClosedConstants i).toAlgebra
  let := polynomialQuotientGlobalSections_finite (originalClosedLiftedIdeal i)
  exact Module.Finite.equiv (originalClosedGlobalSectionsEquiv i).toLinearEquiv

omit [IsClosedImmersion i] in
/-- The coefficient action is EXACTLY the original native projective structure map's actual pullback. -/
theorem originalClosedConstants_eq_coefficientMap :
    originalClosedConstants i =
      ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure K n) := by
  unfold originalClosedConstants
  rw [gradedProjectiveConstants_structure]
  rfl

include hi in
/-- Finite ENTIRE original functions retain the canonical coefficient action of the SAME original morphism. -/
theorem originalClosedGlobalSections_finite_original [IsNoetherianRing K] :
    letI := ProperGeometricGlobalFunctions.sectionsAlgebra (i ≫ projectiveSpaceStructure K n)
    Module.Finite K Γ(X, ⊤) := by
  change @Module.Finite K Γ(X, ⊤) _ _
    (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure K n)).toAlgebra.toModule
  rw [← originalClosedConstants_eq_coefficientMap i]
  exact originalClosedGlobalSections_finite i

end
end Hironaka.Geometry.ProperSteinProjectiveCech
