import Hironaka.Geometry.ProperSteinProjectiveCechQuotientCoefficients
import Hironaka.Geometry.ProperSteinProjectiveCechAlgebraLocalization

/-! # The SAME original quotient native away ring is its literal original module-fraction piece -/

universe u
open CategoryTheory AlgebraicGeometry
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))

omit [LinearOrder I] [Fintype I] in
/-- The SAME original quotient product has its ORIGINAL natural coordinate degree. -/
theorem polynomialQuotientCoordinateProduct_natDegree (S : Finset I) :
    algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal)
      (polynomialCoordinateProduct (K := K) S) ∈
        GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal S.card :=
  (GradedQuotient.gradedMk (MvPolynomial.homogeneousSubmodule I K) J.toIdeal).map_mem
    (polynomialCoordinateProduct_natDegree S)

/-- The SAME actual quotient's ORIGINAL literal integral degree-zero coordinate fractions. -/
abbrev polynomialQuotientCoordinatePiece (S : Finset I) :=
  localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := I))
    (polynomialQuotientIntegralPiece J) (polynomialCoordinateProduct (K := K) S)
    (S.card : ℤ) (polynomialCoordinateProduct_degree S) 0

/-- Native quotient away values retain the SAME actual ordinary localization coefficient action. -/
def polynomialQuotientNativeAwayToOrdinary (S : Finset I) :
    HomogeneousLocalization.Away
        (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)) →ₗ[K]
      Localization.Away
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)) where
  toFun z := z.val
  map_add' z w := HomogeneousLocalization.val_add z w
  map_smul' r z := by
    rw [Algebra.smul_def, HomogeneousLocalization.val_mul,
      polynomialQuotientLocalization_algebraMap_val, Algebra.smul_def]
    rfl

/-- Every ORIGINAL native quotient away value lies in the SAME actual original module fraction piece. -/
def polynomialQuotientNativeAwayToModule (S : Finset I) :
    HomogeneousLocalization.Away
        (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)) →ₗ[K]
      polynomialQuotientCoordinatePiece J S :=
  (((((algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
      (polynomialCoordinateProduct (K := K) S)).symm.restrictScalars K).toLinearMap).comp
    (polynomialQuotientNativeAwayToOrdinary J S))).codRestrict _ (by
      intro z
      obtain ⟨n, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
        (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
        (polynomialQuotientCoordinateProduct_natDegree J S) z
      refine ⟨n, q, ?_, ?_⟩
      · have h := (polynomialQuotientNatIntegralPiece_iff J q (n • S.card)).mp hq
        simpa [nsmul_eq_mul] using h
      · apply (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
          (polynomialCoordinateProduct (K := K) S)).injective
        change (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
            (polynomialCoordinateProduct (K := K) S))
              (LocalizedModule.mk q (homogeneousPowerDenominator (polynomialCoordinateProduct S) n)) =
          (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
            (polynomialCoordinateProduct (K := K) S))
              ((algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
                (polynomialCoordinateProduct (K := K) S)).symm
                  (HomogeneousLocalization.Away.mk _
                    (polynomialQuotientCoordinateProduct_natDegree J S) n q hq).val)
        rw [LinearEquiv.apply_symm_apply, algebraModuleAwayEquiv_mk_power]
        rfl)

omit [LinearOrder I] in
/-- BOTH original literal inverse identities are internally proved for the SAME actual quotient. -/
theorem polynomialQuotientNativeAwayToModule_bijective (S : Finset I) :
    Function.Bijective (polynomialQuotientNativeAwayToModule J S) := by
  constructor
  · intro z w h
    apply HomogeneousLocalization.val_injective
    apply (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
      (polynomialCoordinateProduct (K := K) S)).symm.injective
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨n, q, hq, he⟩ := z.property
    have hqn : q ∈ GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal
        (n • S.card) :=
      (polynomialQuotientNatIntegralPiece_iff J q (n • S.card)).mpr (by
        simpa [nsmul_eq_mul] using hq)
    refine ⟨HomogeneousLocalization.Away.mk _
      (polynomialQuotientCoordinateProduct_natDegree J S) n q hqn, ?_⟩
    apply Subtype.ext
    change (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
      (polynomialCoordinateProduct (K := K) S)).symm _ = z.val
    rw [← he]
    apply (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
      (polynomialCoordinateProduct (K := K) S)).injective
    rw [LinearEquiv.apply_symm_apply, algebraModuleAwayEquiv_mk_power]
    rfl

/-- The actual native quotient away ring is the SAME ORIGINAL degree-zero module fractions. -/
def polynomialQuotientNativeAwayModuleEquiv (S : Finset I) :
    HomogeneousLocalization.Away
        (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)) ≃ₗ[K]
      polynomialQuotientCoordinatePiece J S :=
  LinearEquiv.ofBijective (polynomialQuotientNativeAwayToModule J S)
    (polynomialQuotientNativeAwayToModule_bijective J S)

end
end Hironaka.Geometry.ProperSteinProjectiveCech
