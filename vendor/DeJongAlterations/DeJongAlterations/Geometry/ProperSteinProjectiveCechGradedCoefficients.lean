import DeJongAlterations.Geometry.ProperSteinProjectiveCechQuotientCoefficients

/-! # Native graded original coefficient constants without coordinate-universe identification -/

universe u
open CategoryTheory AlgebraicGeometry
open DeJongAlterations.Geometry.ProjectiveIdeal
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  (𝒜 : ℕ → Submodule K A) (ℬ : ℕ → Submodule K B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The ORIGINAL coefficient map has its actual original degree-zero value. -/
def gradedCoefficientZero : K →+* 𝒜 0 where
  toFun r := ⟨algebraMap K A r, by
    simpa only [Algebra.smul_def, mul_one] using (𝒜 0).smul_mem r (SetLike.one_mem_graded 𝒜)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' r s := Subtype.ext (map_add _ r s)
  map_mul' r s := Subtype.ext (map_mul _ r s)

/-- Actual ORIGINAL graded constants are actual regular fractions at EVERY original prime. -/
def gradedProjectiveConstants (U : (Proj 𝒜).Opens) : K →+* Γ(Proj 𝒜, U) where
  toFun r := ⟨fun x => HomogeneousLocalization.fromZeroRingHom _
    x.val.asHomogeneousIdeal.toIdeal.primeCompl (gradedCoefficientZero 𝒜 r), by
      intro x
      refine ⟨U, x.property, 𝟙 U, 0, gradedCoefficientZero 𝒜 r,
        ⟨1, SetLike.one_mem_graded _⟩,
        fun y => y.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ => rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp (gradedCoefficientZero 𝒜)).map_zero
  map_one' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp (gradedCoefficientZero 𝒜)).map_one
  map_add' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp (gradedCoefficientZero 𝒜)).map_add r s
  map_mul' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp (gradedCoefficientZero 𝒜)).map_mul r s

/-- The SAME ORIGINAL coefficients commute with EVERY actual original restriction. -/
theorem gradedProjectiveConstants_restrict {U V : (Proj 𝒜).Opens} (i : V ⟶ U) (r : K) :
    (Proj 𝒜).presheaf.map i.op (gradedProjectiveConstants 𝒜 U r) =
      gradedProjectiveConstants 𝒜 V r := rfl

/-- The SAME original graded coefficient algebra map commutes with EVERY native original projective pullback. -/
theorem gradedProjectiveConstants_map
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hcoeff : ∀ r : K, f (algebraMap K A r) = algebraMap K B r)
    (U : (Proj 𝒜).Opens) (r : K) :
    (Proj.map f hf).app U (gradedProjectiveConstants 𝒜 U r) =
      gradedProjectiveConstants ℬ ((Proj.map f hf) ⁻¹ᵁ U) r := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change Localization.mk (f (algebraMap K A r)) ⟨f 1, _⟩ =
    Localization.mk (algebraMap K B r) 1
  congr 1
  · exact hcoeff r
  · exact Subtype.ext (map_one f)

attribute [local instance] MvPolynomial.gradedAlgebra
variable {I : Type u}

/-- The previous actual polynomial coefficients are the SAME native graded coefficients. -/
theorem gradedProjectiveConstants_polynomial
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    gradedProjectiveConstants (MvPolynomial.homogeneousSubmodule I K) U =
      homogeneousPolynomialProjConstants U := by
  ext r
  apply Subtype.ext
  funext x
  rfl

/-- The previous actual original quotient coefficients are the SAME native graded coefficients. -/
theorem gradedProjectiveConstants_quotient
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))
    (U : (Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)).Opens) :
    gradedProjectiveConstants (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal) U =
      polynomialQuotientProjConstants J U := by
  ext r
  apply Subtype.ext
  funext x
  rfl

end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
