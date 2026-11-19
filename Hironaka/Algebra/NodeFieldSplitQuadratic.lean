import Hironaka.Algebra.NodeVariableMorseSplitQuadratic
import Hironaka.Algebra.NodeFieldQuadraticChangeSeries
import Hironaka.Algebra.NodeNonsplitPresentationFiber

/-! # An actual original-field factorization internally produces the genuine split node equivalence -/

noncomputable section

namespace Hironaka.Algebra.NodeFieldSplitQuadratic

open MvPowerSeries NodeFormalMorse NodeNonsplit NodeVariableMorse
  NodeFieldQuadraticChangeSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable {K : Type u} [Field K]

/-- The actual original linear form with the specified original coefficients. -/
def linearForm (a b : K) : Series K := C a * X 0 + C b * X 1

/-- The actual whole product has its precise three original quadratic coefficients. -/
theorem product_expansion (a b c d : K) :
    linearForm a b * linearForm c d = quadraticSeries (a * c) (a * d + b * c) (b * d) := by
  simp only [linearForm, quadraticSeries, map_mul, map_add]
  ring

private theorem coefficient0_quadraticSeries (a b c : K) :
    coeff (Finsupp.single 0 2) (quadraticSeries a b c) = a := by
  rw [quadraticSeries_monomials]
  simp only [map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

private theorem coefficient1_quadraticSeries (a b c : K) :
    coeff (Finsupp.single 0 1 + Finsupp.single 1 1) (quadraticSeries a b c) = b := by
  rw [quadraticSeries_monomials]
  simp only [map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

private theorem coefficient2_quadraticSeries (a b c : K) :
    coeff (Finsupp.single 1 2) (quadraticSeries a b c) = c := by
  rw [quadraticSeries_monomials]
  simp only [map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

variable (Q : Quadratic K) (a b c d : K)

/-- The actual WHOLE factorization internally determines the first original coefficient. -/
theorem first_coefficient (hfactor : Q.series = linearForm a b * linearForm c d) : a * c = Q.a0 := by
  have h := congrArg (coeff (Finsupp.single 0 2)) (hfactor.trans (product_expansion a b c d))
  change coeff (Finsupp.single 0 2) (quadraticSeries Q.a0 Q.a1 Q.a2) = _ at h
  rw [coefficient0_quadraticSeries, coefficient0_quadraticSeries] at h
  exact h.symm

/-- The actual WHOLE factorization internally determines the original mixed coefficient, including characteristic two. -/
theorem middle_coefficient (hfactor : Q.series = linearForm a b * linearForm c d) :
    a * d + b * c = Q.a1 := by
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 1))
    (hfactor.trans (product_expansion a b c d))
  change coeff (Finsupp.single 0 1 + Finsupp.single 1 1) (quadraticSeries Q.a0 Q.a1 Q.a2) = _ at h
  rw [coefficient1_quadraticSeries, coefficient1_quadraticSeries] at h
  exact h.symm

/-- The actual WHOLE factorization internally determines the last original coefficient. -/
theorem last_coefficient (hfactor : Q.series = linearForm a b * linearForm c d) : b * d = Q.a2 := by
  have h := congrArg (coeff (Finsupp.single 1 2)) (hfactor.trans (product_expansion a b c d))
  change coeff (Finsupp.single 1 2) (quadraticSeries Q.a0 Q.a1 Q.a2) = _ at h
  rw [coefficient2_quadraticSeries, coefficient2_quadraticSeries] at h
  exact h.symm

/-- The original nondegenerate discriminant is EXACTLY the square of the actual tangent determinant. -/
theorem discriminant_eq_square (hfactor : Q.series = linearForm a b * linearForm c d) :
    Q.a1 ^ 2 - 4 * Q.a0 * Q.a2 = (a * d - b * c) ^ 2 := by
  rw [← first_coefficient Q a b c d hfactor, ← middle_coefficient Q a b c d hfactor,
    ← last_coefficient Q a b c d hfactor]
  ring

/-- No determinant certificate is supplied: actual factorization and the original inverse discriminant derive it. -/
theorem determinant_ne_zero (hfactor : Q.series = linearForm a b * linearForm c d) : a * d - b * c ≠ 0 := by
  intro hd
  apply quadraticDiscriminant_ne_zero Q
  rw [discriminant_eq_square Q a b c d hfactor, hd, zero_pow (by decide : 2 ≠ 0)]

/-- The actual original field-coordinate equivalence is constructed from the SAME factor coefficients. -/
def factorLinearEquiv (hfactor : Q.series = linearForm a b * linearForm c d) : Series K ≃ₐ[K] Series K :=
  linearEquiv a b c d (determinant_ne_zero Q a b c d hfactor)

/-- The actual native product image is the SAME original quadratic, without rescaling. -/
theorem factorLinearEquiv_product (hfactor : Q.series = linearForm a b * linearForm c d) :
    factorLinearEquiv Q a b c d hfactor ((X 0 : Series K) * X 1) = Q.series := by
  change linearEquiv a b c d _ ((X 0 : Series K) * X 1) = _
  rw [map_mul, linearEquiv_apply, linearEquiv_apply, linearSubstitution_X, linearSubstitution_X]
  exact hfactor.symm

/-- The genuine coordinate automorphism takes the SAME original Q to the literal original split product. -/
def splitEquiv (hfactor : Q.series = linearForm a b * linearForm c d) : Series K ≃ₐ[K] Series K :=
  (factorLinearEquiv Q a b c d hfactor).symm

/-- The exact original equation identity holds over the ORIGINAL field. -/
theorem splitEquiv_quadratic (hfactor : Q.series = linearForm a b * linearForm c d) :
    splitEquiv Q a b c d hfactor Q.series = (X 0 : Series K) * X 1 := by
  change (factorLinearEquiv Q a b c d hfactor).symm Q.series = _
  rw [← factorLinearEquiv_product Q a b c d hfactor, AlgEquiv.symm_apply_apply]

/-- EVERY original coefficient is unchanged by the actual original-field coordinate automorphism. -/
theorem splitEquiv_coefficient (hfactor : Q.series = linearForm a b * linearForm c d) (r : K) :
    splitEquiv Q a b c d hfactor (C r) = C r := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (splitEquiv Q a b c d hfactor).commutes r

/-- BOTH original coordinate images are the actual adjugate inverse forms; their determinant was derived internally. -/
theorem splitEquiv_coordinate (hfactor : Q.series = linearForm a b * linearForm c d) (i : Fin 2) :
    splitEquiv Q a b c d hfactor (X i) =
      linearCoordinates ((a * d - b * c)⁻¹ * d) (-((a * d - b * c)⁻¹) * b)
        (-((a * d - b * c)⁻¹) * c) ((a * d - b * c)⁻¹ * a) i := by
  change linearSubstitution ((a * d - b * c)⁻¹ * d) (-((a * d - b * c)⁻¹) * b)
    (-((a * d - b * c)⁻¹) * c) ((a * d - b * c)⁻¹ * a) (X i) = _
  exact linearSubstitution_X _ _ _ _ i

/-- The actual original quadratic quotient is genuinely the split quotient over the SAME original field. -/
def quotientEquiv (hfactor : Q.series = linearForm a b * linearForm c d) :
    QuadraticNode Q ≃ₐ[K] NodeFlatPresentation.SplitNode K :=
  Ideal.quotientEquivAlg _ _ (splitEquiv Q a b c d hfactor) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    exact (splitEquiv_quadratic Q a b c d hfactor).symm)

/-- EVERY original series representative follows the SAME actual coordinate automorphism. -/
theorem quotientEquiv_mk (hfactor : Q.series = linearForm a b * linearForm c d) (f : Series K) :
    quotientEquiv Q a b c d hfactor (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (splitEquiv Q a b c d hfactor f) := rfl

/-- EVERY original field coefficient retains its literal original coefficient class. -/
theorem quotientEquiv_coefficient (hfactor : Q.series = linearForm a b * linearForm c d) (r : K) :
    quotientEquiv Q a b c d hfactor (Ideal.Quotient.mk _ (C r)) =
      Ideal.Quotient.mk _ (C r) := by
  rw [quotientEquiv_mk, splitEquiv_coefficient]

/-- BOTH original coordinates retain precisely the actual adjugate-inverse quotient images. -/
theorem quotientEquiv_coordinate (hfactor : Q.series = linearForm a b * linearForm c d) (i : Fin 2) :
    quotientEquiv Q a b c d hfactor (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _
        (linearCoordinates ((a * d - b * c)⁻¹ * d) (-((a * d - b * c)⁻¹) * b)
          (-((a * d - b * c)⁻¹) * c) ((a * d - b * c)⁻¹ * a) i) := by
  rw [quotientEquiv_mk, splitEquiv_coordinate]

end Hironaka.Algebra.NodeFieldSplitQuadratic
