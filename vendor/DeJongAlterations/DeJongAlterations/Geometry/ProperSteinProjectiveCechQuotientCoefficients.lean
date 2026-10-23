import DeJongAlterations.Geometry.ProperSteinProjectiveCechQuotientGrading
import DeJongAlterations.Geometry.ProjectiveIdealQuotient

/-! # Actual original coefficient actions on the SAME native projective quotient -/

universe u
open CategoryTheory AlgebraicGeometry
open DeJongAlterations.Geometry.ProjectiveIdeal
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))

/-- The actual quotient coefficient has its ORIGINAL constant polynomial as a degree-zero lift. -/
def polynomialQuotientDegreeZeroConstants :
    K →+* GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal 0 where
  toFun r := ⟨algebraMap K (MvPolynomial I K ⧸ J.toIdeal) r,
    Submodule.mem_map.mpr ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C I r, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' r s := Subtype.ext (map_add _ r s)
  map_mul' r s := Subtype.ext (map_mul _ r s)

/-- Actual constants are ORIGINAL native regular fractions at EVERY original quotient prime. -/
def polynomialQuotientProjConstants
    (U : (Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)).Opens) :
    K →+* Γ(Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal), U) where
  toFun r := ⟨fun x => HomogeneousLocalization.fromZeroRingHom _
    x.val.asHomogeneousIdeal.toIdeal.primeCompl (polynomialQuotientDegreeZeroConstants J r), by
      intro x
      refine ⟨U, x.property, 𝟙 U, 0, polynomialQuotientDegreeZeroConstants J r,
        ⟨1, SetLike.one_mem_graded _⟩,
        fun y => y.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ => rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      (polynomialQuotientDegreeZeroConstants J)).map_zero
  map_one' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      (polynomialQuotientDegreeZeroConstants J)).map_one
  map_add' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      (polynomialQuotientDegreeZeroConstants J)).map_add r s
  map_mul' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      (polynomialQuotientDegreeZeroConstants J)).map_mul r s

instance polynomialQuotientProjAlgebra
    (U : (Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)).Opens) :
    Algebra K Γ(Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal), U) :=
  (polynomialQuotientProjConstants J U).toAlgebra

/-- The SAME original constants commute with EVERY actual original restriction. -/
theorem polynomialQuotientProjConstants_restrict
    {U V : (Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)).Opens}
    (i : V ⟶ U) (r : K) :
    (Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)).presheaf.map i.op
      (polynomialQuotientProjConstants J U r) = polynomialQuotientProjConstants J V r := rfl

instance polynomialQuotientHomogeneousLocalizationAlgebra
    (T : Submonoid (MvPolynomial I K ⧸ J.toIdeal)) :
    Algebra K (HomogeneousLocalization
      (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal) T) :=
  ((HomogeneousLocalization.fromZeroRingHom _ _).comp
    (polynomialQuotientDegreeZeroConstants J)).toAlgebra

/-- The actual homogeneous-localization coefficient has its ORIGINAL ordinary localization value. -/
theorem polynomialQuotientLocalization_algebraMap_val
    (T : Submonoid (MvPolynomial I K ⧸ J.toIdeal)) (r : K) :
    (algebraMap K (HomogeneousLocalization
      (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal) T) r).val =
      algebraMap K (Localization T) r := by
  change Localization.mk (algebraMap K (MvPolynomial I K ⧸ J.toIdeal) r) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial I K ⧸ J.toIdeal) (Localization T) r).symm

/-- The actual quotient scheme map retains EVERY original coefficient on EVERY original open. -/
theorem polynomialQuotientCoefficients_triangle
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) (r : K) :
    (GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule I K) J).app U
      (homogeneousPolynomialProjConstants U r) =
        polynomialQuotientProjConstants J
          ((GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule I K) J) ⁻¹ᵁ U) r := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rfl

end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
