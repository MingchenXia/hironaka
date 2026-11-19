import Hironaka.Geometry.ProperSteinProjectiveCechQuotientLocalization

/-! # SAME quotient regular sections and their actual values at EVERY original prime -/

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

/-- The SAME actual native projective homogeneous quotient. -/
abbrev polynomialQuotientScheme : Scheme.{u} :=
  Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)

/-- The actual basic open of the SAME original quotient coordinate product. -/
abbrev polynomialQuotientSubsetOpen (S : Finset I) : (polynomialQuotientScheme J).Opens :=
  Proj.basicOpen (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
    (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S))

/-- Native ORIGINAL regular sections retain the SAME actual quotient coefficient action. -/
def polynomialQuotientNativeAwayBasicOpenEquiv (S : Finset I) (hS : S.Nonempty) :
    HomogeneousLocalization.Away
        (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)) ≃ₐ[K]
      Γ(polynomialQuotientScheme J, polynomialQuotientSubsetOpen J S) := by
  let e := (Proj.basicOpenIsoAway
    (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
    (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S))
    (polynomialQuotientCoordinateProduct_natDegree J S) (Finset.card_pos.mpr hS)).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro r
  apply Subtype.ext
  funext x
  rfl

/-- The original product fraction has its SAME actual full original prime-localization value. -/
def polynomialQuotientCoordinateAtPoint (S : Finset I) (x : polynomialQuotientScheme J)
    (hx : x ∈ polynomialQuotientSubsetOpen J S) :
    Localization.Away
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)) →+*
      Localization x.asHomogeneousIdeal.toIdeal.primeCompl :=
  IsLocalization.map
    (M := Submonoid.powers
      (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)))
    (T := x.asHomogeneousIdeal.toIdeal.primeCompl)
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
    (RingHom.id (MvPolynomial I K ⧸ J.toIdeal))
    (Submonoid.powers_le.mpr ((Proj.mem_basicOpen _ _ _).mp hx))

omit [LinearOrder I] [Fintype I] in
/-- EACH original quotient numerator is retained at EVERY original prime. -/
theorem polynomialQuotientCoordinateAtPoint_algebraMap (S : Finset I)
    (x : polynomialQuotientScheme J) (hx : x ∈ polynomialQuotientSubsetOpen J S)
    (q : MvPolynomial I K ⧸ J.toIdeal) :
    polynomialQuotientCoordinateAtPoint J S x hx
        (algebraMap (MvPolynomial I K ⧸ J.toIdeal)
          (Localization.Away
            (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S))) q) =
      algebraMap (MvPolynomial I K ⧸ J.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) q :=
  IsLocalization.map_eq _ _

omit [LinearOrder I] [Fintype I] in
/-- Native ORIGINAL regular sections evaluate by the SAME actual original localization map. -/
theorem polynomialQuotientNativeAwayBasicOpenEquiv_eval (S : Finset I) (hS : S.Nonempty)
    (z : HomogeneousLocalization.Away
      (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
      (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)))
    (x : polynomialQuotientScheme J) (hx : x ∈ polynomialQuotientSubsetOpen J S) :
    ((polynomialQuotientNativeAwayBasicOpenEquiv J S hS z).val ⟨x, hx⟩).val =
      polynomialQuotientCoordinateAtPoint J S x hx z.val :=
  ProjectiveSpectrum.Proj.awayToSection_apply _ _ z ⟨x, hx⟩

omit [LinearOrder I] in
/-- BOTH actual comparison inverses retain the SAME original ordinary fraction value. -/
theorem polynomialQuotientNativeAwayModuleEquiv_value (S : Finset I)
    (z : HomogeneousLocalization.Away
      (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal)
      (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S))) :
    algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)
      (polynomialQuotientNativeAwayModuleEquiv J S z).val = z.val := by
  change (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S))
    ((algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)).symm z.val) = z.val
  exact LinearEquiv.apply_symm_apply _ _

/-- SAME original degree-zero module fractions are actual regular sections on EACH actual nonempty intersection. -/
def polynomialQuotientRegularPieceEquiv (S : Finset I) (hS : S.Nonempty) :
    polynomialQuotientCoordinatePiece J S ≃ₗ[K]
      Γ(polynomialQuotientScheme J, polynomialQuotientSubsetOpen J S) :=
  (polynomialQuotientNativeAwayModuleEquiv J S).symm.trans
    (polynomialQuotientNativeAwayBasicOpenEquiv J S hS).toLinearEquiv

omit [LinearOrder I] in
/-- Actual regular sections read the SAME original module fraction at EVERY original prime. -/
theorem polynomialQuotientRegularPieceEquiv_eval (S : Finset I) (hS : S.Nonempty)
    (z : polynomialQuotientCoordinatePiece J S)
    (x : polynomialQuotientScheme J) (hx : x ∈ polynomialQuotientSubsetOpen J S) :
    ((polynomialQuotientRegularPieceEquiv J S hS z).val ⟨x, hx⟩).val =
      polynomialQuotientCoordinateAtPoint J S x hx
        (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal)
          (polynomialCoordinateProduct S) z.val) := by
  change ((polynomialQuotientNativeAwayBasicOpenEquiv J S hS
    ((polynomialQuotientNativeAwayModuleEquiv J S).symm z)).val ⟨x, hx⟩).val = _
  rw [polynomialQuotientNativeAwayBasicOpenEquiv_eval]
  congr 1
  have h := polynomialQuotientNativeAwayModuleEquiv_value J S
    ((polynomialQuotientNativeAwayModuleEquiv J S).symm z)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

end
end Hironaka.Geometry.ProperSteinProjectiveCech
