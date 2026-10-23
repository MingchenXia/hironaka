import DeJongAlterations.Algebra.NodeChart
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The domain property of the actual node algebra

The quotient `A[U,V]/(UV-c)` is a domain for a domain `A` and a nonzero element `c`.
The proof constructs the exact evaluation kernel by localization and coordinate saturation.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeDomain

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The actual two-variable node equation in the nested polynomial ring. -/
def nestedEquation (c : A) : A[X][X] := C X * X - C (C c)

/-- The principal ideal of the actual nested node equation. -/
def nestedIdeal (c : A) : Ideal A[X][X] := Ideal.span {nestedEquation c}

/-- Division by the node equation is saturated with respect to the first coordinate. -/
theorem nestedEquation_dvd_of_coordinate_mul (c : A) (hc : c ≠ 0) {P : A[X][X]}
    (h : nestedEquation c ∣ C (X : A[X]) * P) : nestedEquation c ∣ P := by
  obtain ⟨Q, hQ⟩ := h
  have hQzero : Q.map (constantCoeff : A[X] →+* A) = 0 := by
    have hz := congrArg (Polynomial.mapRingHom (constantCoeff : A[X] →+* A)) hQ
    simpa [nestedEquation, hc] using hz
  have hdiv : C (X : A[X]) ∣ Q := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    apply X_dvd_iff.mpr
    have hz := congrArg (fun q : A[X] => q.coeff n) hQzero
    simpa using hz
  obtain ⟨Q', rfl⟩ := hdiv
  refine ⟨Q', ?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr (X_ne_zero : (X : A[X]) ≠ 0))
  calc
    C X * P = nestedEquation c * (C X * Q') := hQ
    _ = C X * (nestedEquation c * Q') := by ring

/-- Saturation holds for every power of the first coordinate. -/
theorem nestedEquation_dvd_of_coordinate_pow_mul (c : A) (hc : c ≠ 0) (n : ℕ)
    {P : A[X][X]} (h : nestedEquation c ∣ C (X : A[X]) ^ n * P) :
    nestedEquation c ∣ P := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using h
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    exact ih (nestedEquation_dvd_of_coordinate_mul c hc h)

/-- The ordinary coefficient localization making the first coordinate invertible. -/
abbrev CoefficientLocalization (A : Type*) [CommRing A] := Localization.Away (X : A[X])

/-- The node evaluation point `c/U` in the actual coefficient localization. -/
def evaluationPoint (c : A) : CoefficientLocalization A :=
  algebraMap A[X] (CoefficientLocalization A) (C c) *
    IsLocalization.Away.invSelf (X : A[X])

/-- Evaluation of the second coordinate at `c/U`. -/
def nestedEvaluation (c : A) : A[X][X] →+* CoefficientLocalization A :=
  Polynomial.eval₂RingHom (algebraMap A[X] (CoefficientLocalization A)) (evaluationPoint c)

omit [IsDomain A] in
/-- The evaluation point satisfies the original node equation. -/
theorem coordinate_mul_evaluationPoint (c : A) :
    algebraMap A[X] (CoefficientLocalization A) X * evaluationPoint c =
      algebraMap A[X] (CoefficientLocalization A) (C c) := by
  rw [evaluationPoint]
  calc
    _ = algebraMap A[X] (CoefficientLocalization A) (C c) *
        (algebraMap A[X] (CoefficientLocalization A) X *
          IsLocalization.Away.invSelf (X : A[X])) := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

omit [IsDomain A] in
/-- The original polynomial equation evaluates to zero. -/
theorem nestedEvaluation_equation (c : A) : nestedEvaluation c (nestedEquation c) = 0 := by
  simp [nestedEvaluation, nestedEquation, coordinate_mul_evaluationPoint]

attribute [local instance] Polynomial.algebra

/-- The exact kernel calculation, obtained from coordinate saturation and localization. -/
theorem nestedEvaluation_eq_zero_iff (c : A) (hc : c ≠ 0) (P : A[X][X]) :
    nestedEvaluation c P = 0 ↔ nestedEquation c ∣ P := by
  constructor
  · intro hP
    let L := CoefficientLocalization A
    let φ : A[X] →+* L := algebraMap A[X] L
    let M : Submonoid A[X][X] := (Submonoid.powers (X : A[X])).map Polynomial.C
    let : IsLocalization M L[X] := Polynomial.isLocalization _ _
    have hlin : X - C (evaluationPoint c) ∣ P.map φ := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (P.map φ).eval (evaluationPoint c) = 0
      rw [Polynomial.eval_map]
      exact hP
    have hfactor : (nestedEquation c).map φ =
        C (φ X) * (X - C (evaluationPoint c)) := by
      simp only [nestedEquation, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, mul_sub, ← C_mul]
      rw [coordinate_mul_evaluationPoint]
    have hu : IsUnit (C (φ X) : L[X]) :=
      (IsLocalization.Away.algebraMap_isUnit (X : A[X])).map Polynomial.C
    have hdiv : (nestedEquation c).map φ ∣ P.map φ := by
      obtain ⟨u, hu⟩ := hu
      obtain ⟨Q, hQ⟩ := hlin
      refine ⟨(↑u⁻¹ : L[X]) * Q, ?_⟩
      rw [hfactor, ← hu, hQ]
      simp [mul_assoc, mul_left_comm]
    have hmem : algebraMap A[X][X] L[X] P ∈
        (nestedIdeal c).map (algebraMap A[X][X] L[X]) := by
      rw [nestedIdeal, Ideal.map_span, Set.image_singleton]
      apply Ideal.mem_span_singleton.mpr
      exact hdiv
    obtain ⟨m, hm, hmp⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M L[X] (nestedIdeal c) P).mp hmem
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hm
    obtain ⟨n, rfl⟩ := hs
    have hpow : nestedEquation c ∣ C (X : A[X]) ^ n * P := by
      rw [← map_pow]
      exact Ideal.mem_span_singleton.mp hmp
    exact nestedEquation_dvd_of_coordinate_pow_mul c hc n hpow
  · rintro ⟨Q, rfl⟩
    rw [map_mul, nestedEvaluation_equation, zero_mul]

/-- The coefficient localization is a domain, since the coordinate being inverted is nonzero. -/
instance coefficientLocalization_isDomain : IsDomain (CoefficientLocalization A) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero : (X : A[X]) ≠ 0))

/-- The actual quotient embeds in the ordinary coordinate localization by the proved kernel. -/
def nestedQuotientEmbedding (c : A) (hc : c ≠ 0) :
    (A[X][X] ⧸ nestedIdeal c) →+* CoefficientLocalization A :=
  Ideal.Quotient.lift (nestedIdeal c) (nestedEvaluation c) (fun P hP =>
    (nestedEvaluation_eq_zero_iff c hc P).mpr (Ideal.mem_span_singleton.mp hP))

/-- The quotient embedding is injective on the entire quotient ring. -/
theorem nestedQuotientEmbedding_injective (c : A) (hc : c ≠ 0) :
    Function.Injective (nestedQuotientEmbedding c hc) := by
  intro x y hxy
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  apply (nestedEvaluation_eq_zero_iff c hc (P - Q)).mp
  change nestedEvaluation c P = nestedEvaluation c Q at hxy
  rw [map_sub, hxy, sub_self]

/-- The genuine nested node quotient is a domain; no unique factorization hypothesis is needed. -/
theorem nestedQuotient_isDomain (c : A) (hc : c ≠ 0) :
    IsDomain (A[X][X] ⧸ nestedIdeal c) :=
  (nestedQuotientEmbedding_injective c hc).isDomain

/-- The original coefficient map into the actual nested quotient is injective. -/
theorem algebraMap_nestedQuotient_injective (c : A) (hc : c ≠ 0) :
    Function.Injective (algebraMap A (A[X][X] ⧸ nestedIdeal c) :
      A →+* (A[X][X] ⧸ nestedIdeal c)) := by
  intro a b hab
  have h := congrArg (nestedQuotientEmbedding c hc) hab
  rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap] at h
  have h' : algebraMap A[X] (CoefficientLocalization A) (C a) =
      algebraMap A[X] (CoefficientLocalization A) (C b) := by
    simpa [nestedQuotientEmbedding, nestedEvaluation, Polynomial.algebraMap_apply] using h
  exact Polynomial.C_injective (IsLocalization.injective (CoefficientLocalization A)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero : (X : A[X]) ≠ 0)) h')

/-- The standard two-variable polynomial algebra is the actual nested polynomial algebra. -/
def polynomialEquiv : MvPolynomial (Fin 2) A ≃ₐ[A] A[X][X] :=
  (MvPolynomial.finSuccEquiv A 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))

omit [IsDomain A] in
/-- The polynomial equivalence preserves the original node equation. -/
theorem polynomialEquiv_equation (c : A) :
    polynomialEquiv (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c) =
      nestedEquation c := by
  have hX1 : (MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X 1) =
      C (MvPolynomial.X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := A) (j := (0 : Fin 1))
  have hC : (MvPolynomial.finSuccEquiv A 1) (MvPolynomial.C c) =
      C (MvPolynomial.C c) := by
    simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  simp [polynomialEquiv, MvPolynomial.finSuccEquiv_X_zero, hX1, hC,
    MvPolynomial.uniqueAlgEquiv_apply,
    Polynomial.mapAlgEquiv, nestedEquation]

/-- Literal two-variable node quotients and nested node quotients are canonically equivalent. -/
def nodeQuotientEquiv (c : A) :
    (MvPolynomial (Fin 2) A ⧸ NodeChart.uChartIdeal A c) ≃ₐ[A]
      (A[X][X] ⧸ nestedIdeal c) :=
  Ideal.quotientEquivAlg _ _ polynomialEquiv (by
    rw [NodeChart.uChartIdeal, Ideal.map_span, Set.image_singleton]
    change nestedIdeal c = Ideal.span {polynomialEquiv
      (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c)}
    rw [polynomialEquiv_equation]
    rfl)

/-- The actual `MvPolynomial (Fin 2)` node quotient used by the chart identities is a domain. -/
theorem nodeQuotient_isDomain (c : A) (hc : c ≠ 0) :
    IsDomain (MvPolynomial (Fin 2) A ⧸ NodeChart.uChartIdeal A c) := by
  let := nestedQuotient_isDomain c hc
  exact (nodeQuotientEquiv c).injective.isDomain

/-- The canonical coefficient map into the literal two-variable node quotient is injective. -/
theorem algebraMap_nodeQuotient_injective (c : A) (hc : c ≠ 0) :
    Function.Injective (algebraMap A (MvPolynomial (Fin 2) A ⧸ NodeChart.uChartIdeal A c)) := by
  intro a b hab
  apply algebraMap_nestedQuotient_injective c hc
  simpa only [AlgEquiv.commutes] using congrArg (nodeQuotientEquiv c) hab

omit [IsDomain A] in
/-- The coordinates in the literal quotient satisfy their original product equation. -/
theorem nodeCoordinateProduct (c : A) :
    Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X 0) *
      Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X 1) =
        algebraMap A (MvPolynomial (Fin 2) A ⧸ NodeChart.uChartIdeal A c) c := by
  change Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X 0) *
    Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X 1) =
      Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.C c)
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  exact Ideal.mem_span_singleton_self _

/-- Both actual node coordinates are nonzero, so either can serve as a blowup chart denominator. -/
theorem nodeCoordinate_ne_zero (c : A) (hc : c ≠ 0) (i : Fin 2) :
    Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X i) ≠ 0 := by
  let := nodeQuotient_isDomain c hc
  have hmul : Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X 0) *
      Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X 1) ≠ 0 := by
    rw [nodeCoordinateProduct]
    exact (map_ne_zero_iff _ (algebraMap_nodeQuotient_injective c hc)).mpr hc
  fin_cases i
  · exact (mul_ne_zero_iff.mp hmul).1
  · exact (mul_ne_zero_iff.mp hmul).2

end DeJongAlterations.Algebra.NodeDomain
