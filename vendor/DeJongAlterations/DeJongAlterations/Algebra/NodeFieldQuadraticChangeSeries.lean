import DeJongAlterations.Algebra.NodeFieldQuadraticChange
import DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet

/-! # Actual quadratic coefficient changes from the original zero-constant series

Both tangent linear parts and the full cubic substitution error are internally
produced. No tangent matrix, linear approximation, or coefficient-output
certificate is supplied. All formulas include characteristic two.
-/

noncomputable section

open MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldQuadraticChangeSeries

open NodeFormalMorse NodeVariableMorse NodeFieldQuadraticChange NodeFieldCotangentGeneratorsJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- The tangent part is extracted from the SAME original two actual linear coefficients. -/
def linearPart (f : Series K) : Series K :=
  coordinateRepresentative K (0, fun i => coeff (Finsupp.single i 1) f)

/-- This internally constructed representative is the literal original linear series. -/
theorem linearPart_eq (f : Series K) :
    linearPart f = C (coeff (Finsupp.single 0 1) f) * X 0 +
      C (coeff (Finsupp.single 1 1) f) * X 1 := by
  change monomial 0 (0 : K) + monomial (Finsupp.single 0 1) (coeff (Finsupp.single 0 1) f) +
    monomial (Finsupp.single 1 1) (coeff (Finsupp.single 1 1) f) =
      monomial 0 (coeff (Finsupp.single 0 1) f) * monomial (Finsupp.single 0 1) 1 +
        monomial 0 (coeff (Finsupp.single 1 1) f) * monomial (Finsupp.single 1 1) 1
  simp only [map_zero, zero_add, monomial_mul_monomial, mul_one]

/-- The full actual internally constructed linear part belongs to the original variable ideal. -/
theorem linearPart_mem (f : Series K) : linearPart f ∈ variableIdeal K := by
  rw [linearPart_eq]
  exact (variableIdeal K).add_mem
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self 0)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self 1)))

/-- Original zero constant alone internally gives the full quadratic-order linear-part residual. -/
theorem sub_linearPart_mem_square (f : Series K) (hf : constantCoeff f = 0) :
    f - linearPart f ∈ variableIdeal K ^ 2 := by
  apply (mem_variableSquare_iff K _).mpr
  rw [map_sub, linearPart, coordinates_representative]
  apply Prod.ext
  · change constantCoeff f - 0 = 0
    simpa only [sub_zero] using hf
  · funext i
    change coeff (Finsupp.single i 1) f - coeff (Finsupp.single i 1) f = 0
    exact sub_self _

/-- Literal evaluation of the original quadratic using its SAME original coefficient map. -/
def composition (a b c : K) (x y : Series K) : Series K :=
  C a * x ^ 2 + C b * x * y + C c * y ^ 2

/-- The full product error is cubic from only the two actual zero constants. -/
theorem product_linearPart_error (x y : Series K)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    x * y - linearPart x * linearPart y ∈ variableIdeal K ^ 3 := by
  have hex : x - linearPart x ∈ variableIdeal K ^ 2 := sub_linearPart_mem_square x hx
  have hey : y - linearPart y ∈ variableIdeal K ^ 2 := sub_linearPart_mem_square y hy
  have h1 : (x - linearPart x) * y ∈ variableIdeal K ^ 3 := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul hex (mem_variableIdeal_of_constantCoeff_eq_zero hy)
  have h2 : linearPart x * (y - linearPart y) ∈ variableIdeal K ^ 3 := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul (linearPart_mem x) hey
  have he : x * y - linearPart x * linearPart y =
      (x - linearPart x) * y + linearPart x * (y - linearPart y) := by ring
  rw [he]
  exact (variableIdeal K ^ 3).add_mem h1 h2

/-- The ENTIRE actual quadratic substitution error lies in the original cubic variable ideal. -/
theorem composition_linearPart_error (a b c : K) (x y : Series K)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    composition a b c x y - composition a b c (linearPart x) (linearPart y) ∈
      variableIdeal K ^ 3 := by
  have he : composition a b c x y - composition a b c (linearPart x) (linearPart y) =
      C a * (x * x - linearPart x * linearPart x) +
        C b * (x * y - linearPart x * linearPart y) +
          C c * (y * y - linearPart y * linearPart y) := by
    simp only [composition]
    ring
  rw [he]
  exact (variableIdeal K ^ 3).add_mem
    ((variableIdeal K ^ 3).add_mem
      (Ideal.mul_mem_left _ _ (product_linearPart_error x x hx hx))
      (Ideal.mul_mem_left _ _ (product_linearPart_error x y hx hy)))
    (Ideal.mul_mem_left _ _ (product_linearPart_error y y hy hy))

/-- The literal original quadratic with the specified actual coefficients. -/
def quadraticSeries (a b c : K) : Series K := C a * X 0 ^ 2 + C b * X 0 * X 1 + C c * X 1 ^ 2

/-- Its actual native monomials, used only for exact coefficient readback. -/
theorem quadraticSeries_monomials (a b c : K) :
    quadraticSeries a b c = monomial (Finsupp.single 0 2) a +
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) b + monomial (Finsupp.single 1 2) c := by
  rw [quadraticSeries, X_pow_eq, X_pow_eq]
  change monomial 0 a * monomial (Finsupp.single 0 2) 1 +
    monomial 0 b * monomial (Finsupp.single 0 1) 1 * monomial (Finsupp.single 1 1) 1 +
      monomial 0 c * monomial (Finsupp.single 1 2) 1 = _
  simp only [monomial_mul_monomial, zero_add, mul_one]

/-- Actual linear substitution gives the three prescribed original coefficient polynomials exactly. -/
theorem linear_composition (a b c : K) (x y : Series K) :
    composition a b c (linearPart x) (linearPart y) =
      quadraticSeries
        (firstCoefficient a b c (coeff (Finsupp.single 0 1) x) (coeff (Finsupp.single 0 1) y))
        (middleCoefficient a b c (coeff (Finsupp.single 0 1) x) (coeff (Finsupp.single 1 1) x)
          (coeff (Finsupp.single 0 1) y) (coeff (Finsupp.single 1 1) y))
        (lastCoefficient a b c (coeff (Finsupp.single 1 1) x) (coeff (Finsupp.single 1 1) y)) := by
  rw [linearPart_eq x, linearPart_eq y]
  simp only [composition, quadraticSeries, firstCoefficient, middleCoefficient, lastCoefficient,
    map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The actual cubic error forces equality of EVERY original coefficient below degree three. -/
theorem coeff_eq_of_sub_mem_cube (f g : Series K) (h : f - g ∈ variableIdeal K ^ 3)
    (d : Fin 2 →₀ ℕ) (hd : d.degree < 3) : coeff d f = coeff d g := by
  have hz : coeff d (f - g) = 0 :=
    coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd)
      ((mem_variableIdeal_pow_iff_order 3 _).mp h))
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- The actual first quadratic coefficient is computed from only the two original zero constants. -/
theorem first_coefficient (a b c : K) (x y : Series K)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    coeff (Finsupp.single 0 2) (composition a b c x y) =
      firstCoefficient a b c (coeff (Finsupp.single 0 1) x) (coeff (Finsupp.single 0 1) y) := by
  rw [coeff_eq_of_sub_mem_cube _ _ (composition_linearPart_error a b c x y hx hy)
    (Finsupp.single 0 2) (by simp), linear_composition, quadraticSeries_monomials]
  simp only [map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

/-- The actual mixed quadratic coefficient includes characteristic two without division by two. -/
theorem middle_coefficient (a b c : K) (x y : Series K)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    coeff (Finsupp.single 0 1 + Finsupp.single 1 1) (composition a b c x y) =
      middleCoefficient a b c (coeff (Finsupp.single 0 1) x) (coeff (Finsupp.single 1 1) x)
        (coeff (Finsupp.single 0 1) y) (coeff (Finsupp.single 1 1) y) := by
  rw [coeff_eq_of_sub_mem_cube _ _ (composition_linearPart_error a b c x y hx hy)
    (Finsupp.single 0 1 + Finsupp.single 1 1) (by simp), linear_composition, quadraticSeries_monomials]
  simp only [map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

/-- The actual last quadratic coefficient keeps the same original coefficient and coordinate triangle. -/
theorem last_coefficient (a b c : K) (x y : Series K)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    coeff (Finsupp.single 1 2) (composition a b c x y) =
      lastCoefficient a b c (coeff (Finsupp.single 1 1) x) (coeff (Finsupp.single 1 1) y) := by
  rw [coeff_eq_of_sub_mem_cube _ _ (composition_linearPart_error a b c x y hx hy)
    (Finsupp.single 1 2) (by simp), linear_composition, quadraticSeries_monomials]
  simp only [map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

/-- SAME actual coordinate-series determinant and diagonal vanishing INTERNALLY force original nondegeneracy. -/
theorem discriminant_ne_zero_of_diagonal_coefficients (a b c : K) (x y : Series K)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (hdet : determinant (coeff (Finsupp.single 0 1) x) (coeff (Finsupp.single 1 1) x)
      (coeff (Finsupp.single 0 1) y) (coeff (Finsupp.single 1 1) y) ≠ 0)
    (habc : ¬ (a = 0 ∧ b = 0 ∧ c = 0))
    (hfirst : coeff (Finsupp.single 0 2) (composition a b c x y) = 0)
    (hlast : coeff (Finsupp.single 1 2) (composition a b c x y) = 0) :
    b ^ 2 - 4 * a * c ≠ 0 := by
  apply NodeFieldQuadraticChange.discriminant_ne_zero a b c
    (coeff (Finsupp.single 0 1) x) (coeff (Finsupp.single 1 1) x)
    (coeff (Finsupp.single 0 1) y) (coeff (Finsupp.single 1 1) y) hdet habc
  · rwa [← first_coefficient a b c x y hx hy]
  · rwa [← last_coefficient a b c x y hx hy]

end DeJongAlterations.Algebra.NodeFieldQuadraticChangeSeries
