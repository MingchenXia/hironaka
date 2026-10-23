import DeJongAlterations.Algebra.NodeVariableMorseComplete

/-! # The original formal equation determines its own actual quadratic jet and cubic residual -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- The original coefficient at the first quadratic monomial. -/
def quadraticCoefficient0 (f : Series K) : K := coeff (Finsupp.single 0 2) f

/-- The original actual mixed quadratic coefficient. -/
def quadraticCoefficient1 (f : Series K) : K := coeff (Finsupp.single 0 1 + Finsupp.single 1 1) f

/-- The original coefficient at the second quadratic monomial. -/
def quadraticCoefficient2 (f : Series K) : K := coeff (Finsupp.single 1 2) f

/-- The actual quadratic homogeneous part extracted internally from the original equation. -/
def quadraticJet (f : Series K) : Series K :=
  monomial (Finsupp.single 0 2) (quadraticCoefficient0 f) +
    monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (quadraticCoefficient1 f) +
    monomial (Finsupp.single 1 2) (quadraticCoefficient2 f)

@[simp]
private theorem constantCoeff_monomialJet (d : Fin 2 →₀ ℕ) (a : K) :
    constantCoeff (monomial d a) = if (0 : Fin 2 →₀ ℕ) = d then a else 0 :=
  coeff_monomial 0 d a

/-- The original equation's internally constructed residual has actual cubic variable order. -/
theorem sub_quadraticJet_mem_pow (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0) :
    f - quadraticJet f ∈ variableIdeal K ^ 3 := by
  apply (mem_variableIdeal_pow_iff_order 3 _).mpr
  apply nat_le_order
  intro d hd
  have hd' : d 0 + d 1 < 3 := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  have hb0 : d 0 ≤ 2 := by omega
  have hb1 : d 1 ≤ 2 := by omega
  have he : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
    ext i
    fin_cases i <;> simp
  rw [he]
  interval_cases h00 : d 0 <;> interval_cases h11 : d 1 <;> try omega
  all_goals simp [quadraticJet, quadraticCoefficient0, quadraticCoefficient1, quadraticCoefficient2,
    coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_two, hc, h0, h1]

/-- The actual original quadratic-jet discriminant. -/
def jetDiscriminant (f : Series K) : K :=
  quadraticCoefficient1 f ^ 2 - 4 * quadraticCoefficient0 f * quadraticCoefficient2 f

/-- Nondegeneracy of the original jet internally supplies its original inverse discriminant. -/
def jetQuadratic (f : Series K) (hΔ : jetDiscriminant f ≠ 0) : Quadratic K :=
  Quadratic.ofCoefficients (quadraticCoefficient0 f) (quadraticCoefficient1 f)
    (quadraticCoefficient2 f) (isUnit_iff_ne_zero.mpr hΔ)

/-- The internally extracted original quadratic is exactly the original quadratic homogeneous jet. -/
theorem jetQuadratic_series (f : Series K) (hΔ : jetDiscriminant f ≠ 0) :
    (jetQuadratic f hΔ).series = quadraticJet f := by
  change C (quadraticCoefficient0 f) * X 0 ^ 2 +
    C (quadraticCoefficient1 f) * X 0 * X 1 + C (quadraticCoefficient2 f) * X 1 ^ 2 = _
  rw [X_pow_eq, X_pow_eq]
  change monomial 0 (quadraticCoefficient0 f) * monomial (Finsupp.single 0 2) 1 +
    monomial 0 (quadraticCoefficient1 f) * monomial (Finsupp.single 0 1) 1 *
      monomial (Finsupp.single 1 1) 1 +
    monomial 0 (quadraticCoefficient2 f) * monomial (Finsupp.single 1 2) 1 = _
  simp only [monomial_mul_monomial, zero_add, mul_one]
  rfl

/-- The actual same-field automorphism classifying the original equation by its own actual jet. -/
def equationNormalFormEquiv (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) : Series K ≃ₐ[K] Series K :=
  plusNormalFormEquiv (jetQuadratic f hΔ) (f - quadraticJet f) (sub_quadraticJet_mem_pow f hc h0 h1)

/-- The original equation itself is actually carried to its internally extracted original quadratic. -/
theorem equationNormalFormEquiv_equation (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    equationNormalFormEquiv f hc h0 h1 hΔ f = quadraticJet f := by
  have he := plusNormalFormEquiv_equation (jetQuadratic f hΔ)
    (f - quadraticJet f) (sub_quadraticJet_mem_pow f hc h0 h1)
  rw [jetQuadratic_series, add_sub_cancel] at he
  exact he

/-- The actual original equation quotient has the actual original quadratic-jet model. -/
def equationQuotientEquiv (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    (Series K ⧸ Ideal.span {f}) ≃ₐ[K] Series K ⧸ Ideal.span {quadraticJet f} :=
  Ideal.quotientEquivAlg _ _ (equationNormalFormEquiv f hc h0 h1 hΔ) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    change quadraticJet f = equationNormalFormEquiv f hc h0 h1 hΔ f
    exact (equationNormalFormEquiv_equation f hc h0 h1 hΔ).symm)

/-- The original equation's constructed normal form retains its original tangent coordinates. -/
theorem equationNormalFormEquiv_coordinate (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) (i : Fin 2) :
    equationNormalFormEquiv f hc h0 h1 hΔ (X i) - X i ∈ variableIdeal K ^ 2 :=
  normalFormEquiv_coordinate (jetQuadratic f hΔ) (-(f - quadraticJet f))
    ((variableIdeal K ^ 3).neg_mem (sub_quadraticJet_mem_pow f hc h0 h1)) i

/-- Its actual original inverse retains the same original tangent coordinates. -/
theorem equationNormalFormEquiv_symm_coordinate (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) (i : Fin 2) :
    (equationNormalFormEquiv f hc h0 h1 hΔ).symm (X i) - X i ∈ variableIdeal K ^ 2 :=
  deformationEquiv_coordinate (jetQuadratic f hΔ) (-(f - quadraticJet f))
    ((variableIdeal K ^ 3).neg_mem (sub_quadraticJet_mem_pow f hc h0 h1)) i

/-- Source-facing actual original-equation classification, without a supplied residual or model. -/
theorem exists_equation_normal_form (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    ∃ e : Series K ≃ₐ[K] Series K, e f = quadraticJet f ∧
      (∀ i : Fin 2, e (X i) - X i ∈ variableIdeal K ^ 2) ∧
      (∀ i : Fin 2, e.symm (X i) - X i ∈ variableIdeal K ^ 2) :=
  ⟨equationNormalFormEquiv f hc h0 h1 hΔ, equationNormalFormEquiv_equation f hc h0 h1 hΔ,
    equationNormalFormEquiv_coordinate f hc h0 h1 hΔ,
    equationNormalFormEquiv_symm_coordinate f hc h0 h1 hΔ⟩

end DeJongAlterations.Algebra.NodeVariableMorse
