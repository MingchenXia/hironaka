import DeJongAlterations.Algebra.NodeSingularGradient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual quadratic node coordinate quotient

The original constant-coefficient map gives the actual quotient by the
quadratic gradient ideal, with no supplied singular-ideal certificate.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeSingular

open MvPowerSeries NodeFormalMorse NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

abbrev equationIdeal (Q : Quadratic R) (h : R) : Ideal (Series R) :=
  Ideal.span {Q.series - C h}

/-- The actual completed quadratic node ring over the original coefficients. -/
abbrev Node (Q : Quadratic R) (h : R) := Series R ⧸ equationIdeal Q h

/-- The two original coordinate classes. -/
def coordinate (Q : Quadratic R) (h : R) (i : Fin 2) : Node Q h :=
  Ideal.Quotient.mk _ (X i)

/-- The actual ideal of the two coordinate classes. -/
def coordinateIdeal (Q : Quadratic R) (h : R) : Ideal (Node Q h) :=
  Ideal.span {coordinate Q h 0, coordinate Q h 1}

/-- The actual quadratic gradient ideal in the literal node quotient. -/
def gradientIdeal (Q : Quadratic R) (h : R) : Ideal (Node Q h) :=
  let Q' := Q.map (algebraMap R (Node Q h))
  Ideal.span {leftGradient Q' (coordinate Q h 0) (coordinate Q h 1),
    rightGradient Q' (coordinate Q h 0) (coordinate Q h 1)}

/-- Discriminant invertibility identifies the actual quotient gradient ideal. -/
theorem gradientIdeal_eq (Q : Quadratic R) (h : R) :
    gradientIdeal Q h = coordinateIdeal Q h :=
  gradientIdeal_eq_coordinateIdeal _ _ _

/-- Actual original constant coefficient followed by reduction modulo the parameter. -/
def constantReduction (h : R) : Series R →ₐ[R] R ⧸ Ideal.span {h} where
  __ := (Ideal.Quotient.mk _).comp constantCoeff
  commutes' _r := rfl

/-- The original equation is killed by actual parameter-zero evaluation. -/
def nodeEvaluation (Q : Quadratic R) (h : R) : Node Q h →ₐ[R] R ⧸ Ideal.span {h} :=
  Ideal.Quotient.liftₐ _ (constantReduction h) (by
    change equationIdeal Q h ≤ RingHom.ker (constantReduction h).toRingHom
    apply Ideal.span_le.mpr
    rintro f rfl
    change Ideal.Quotient.mk (Ideal.span {h}) (constantCoeff (Q.series - C h)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simp [Quadratic.series, Quadratic.value, Quadratic.map])

@[simp]
theorem nodeEvaluation_mk (Q : Quadratic R) (h : R) (f : Series R) :
    nodeEvaluation Q h (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk (Ideal.span {h}) (constantCoeff f) := rfl

@[simp]
theorem nodeEvaluation_coordinate (Q : Quadratic R) (h : R) (i : Fin 2) :
    nodeEvaluation Q h (coordinate Q h i) = 0 := by
  simp [coordinate]

/-- Original coefficients give all elements of the actual parameter quotient. -/
theorem nodeEvaluation_surjective (Q : Quadratic R) (h : R) :
    Function.Surjective (nodeEvaluation Q h) := by
  intro a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ (C r), by simp⟩

/-- The original relation puts the original parameter in the actual coordinate ideal. -/
theorem parameter_mem_coordinateIdeal (Q : Quadratic R) (h : R) :
    algebraMap R (Node Q h) h ∈ coordinateIdeal Q h := by
  have hz : Ideal.Quotient.mk (equationIdeal Q h) (Q.series - C h) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub, sub_eq_zero] at hz
  change Ideal.Quotient.mk _ (C h) ∈ coordinateIdeal Q h
  rw [← hz]
  let J : Ideal (Node Q h) := coordinateIdeal Q h
  have h0 : coordinate Q h 0 ∈ J := Ideal.subset_span (by simp)
  have h1 : coordinate Q h 1 ∈ J := Ideal.subset_span (by simp)
  change Ideal.Quotient.mk _
    (C Q.a0 * X 0 ^ 2 + C Q.a1 * X 0 * X 1 + C Q.a2 * X 1 ^ 2) ∈ J
  simp only [map_add, map_mul, map_pow]
  simp only [pow_two]
  exact J.add_mem (J.add_mem
    (J.mul_mem_left _ (J.mul_mem_left _ h0)) (J.mul_mem_left _ h1))
    (J.mul_mem_left _ (J.mul_mem_left _ h1))

/-- The kernel is the whole actual coordinate ideal, not merely its radical. -/
theorem nodeEvaluation_kernel (Q : Quadratic R) (h : R) :
    RingHom.ker (nodeEvaluation Q h).toRingHom = coordinateIdeal Q h := by
  apply le_antisymm
  · intro b hb
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hc : constantCoeff f ∈ Ideal.span {h} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hc
    have hconst : Ideal.Quotient.mk (equationIdeal Q h) (C (constantCoeff f)) ∈
        coordinateIdeal Q h := by
      rw [hr, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (parameter_mem_coordinateIdeal Q h)
    have he := congrArg (Ideal.Quotient.mk (equationIdeal Q h)) (decomposition f)
    rw [he]
    simp only [map_add, map_mul]
    apply Ideal.add_mem _ (Ideal.add_mem _ hconst ?_) ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp [coordinate]))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp [coordinate]))
  · apply Ideal.span_le.mpr
    rintro b (rfl | rfl) <;> exact nodeEvaluation_coordinate _ _ _

/-- The actual gradient quotient is canonically the original parameter zero locus. -/
def gradientQuotientEquiv (Q : Quadratic R) (h : R) :
    (Node Q h ⧸ gradientIdeal Q h) ≃ₐ[R] R ⧸ Ideal.span {h} :=
  (Ideal.quotientEquivAlgOfEq R ((gradientIdeal_eq Q h).trans (nodeEvaluation_kernel Q h).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (nodeEvaluation_surjective Q h))

@[simp]
theorem gradientQuotientEquiv_coefficient (Q : Quadratic R) (h r : R) :
    gradientQuotientEquiv Q h
      (Ideal.Quotient.mk (gradientIdeal Q h) (Ideal.Quotient.mk (equationIdeal Q h) (C r))) =
      Ideal.Quotient.mk (Ideal.span {h}) r := by
  rfl

end DeJongAlterations.Algebra.NodeSingular
