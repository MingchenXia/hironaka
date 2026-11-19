import Hironaka.Algebra.NodeFieldIsotropicQuadratic
import Hironaka.Algebra.NodeFieldQuadraticSource
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases

/-! A whole actual original-field smooth branch internally gives an isotropic tangent. -/

noncomputable section

namespace Hironaka.Algebra.NodeFieldSmoothBranch

open IsLocalRing NodeNonsplit NodeFormalMorse NodeVariableMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K] (q : Quadratic K)

private theorem quadratic_zero_constant : MvPowerSeries.constantCoeff q.series = 0 := by
  simp [Quadratic.series, Quadratic.value, Quadratic.map]

local instance : Nontrivial (QuadraticNode q) :=
  NodeFieldQuadraticSource.equationNontrivial K q.series (quadratic_zero_constant q)
local instance : IsLocalRing (QuadraticNode q) :=
  NodeFieldQuadraticSource.equationLocalRing K q.series (quadratic_zero_constant q)

variable (φ : QuadraticNode q →ₐ[K] PowerSeries K)

/-- The actual two original coordinates follow the WHOLE original branch map. -/
def coordinate (i : Fin 2) : PowerSeries K :=
  φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))

/-- The actual native first coefficients of the SAME two coordinate images. -/
def tangent (i : Fin 2) : K := PowerSeries.coeff 1 (coordinate q φ i)

private theorem source_maximalIdeal :
    maximalIdeal (QuadraticNode q) =
      Ideal.span (Set.range fun i : Fin 2 => Ideal.Quotient.mk _ (MvPowerSeries.X i)) := by
  rw [NodeFieldQuadraticSource.equation_maximalIdeal K q.series (quadratic_zero_constant q)]
  rw [variableIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Actual surjectivity carries the ENTIRE original maximal ideal to its actual branch image. -/
private theorem coordinate_span (hφ : Function.Surjective φ) :
    Ideal.span (Set.range (coordinate q φ)) = maximalIdeal (PowerSeries K) := by
  have h := map_maximalIdeal_of_surjective φ.toRingHom hφ
  rw [source_maximalIdeal q, Ideal.map_span, ← Set.range_comp] at h
  exact h

/-- Both actual original coordinate images have zero constant term, internally. -/
theorem coordinate_constantCoeff (hφ : Function.Surjective φ) (i : Fin 2) :
    PowerSeries.constantCoeff (coordinate q φ i) = 0 := by
  have hi : coordinate q φ i ∈ maximalIdeal (PowerSeries K) := by
    rw [← coordinate_span q φ hφ]
    exact Ideal.subset_span ⟨i, rfl⟩
  rw [PowerSeries.maximalIdeal_eq_span_X] at hi
  exact PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp hi)

/-- The SAME actual branch map INTERNALLY produces a nonzero original tangent vector. -/
theorem tangent_nonzero (hφ : Function.Surjective φ) :
    tangent q φ 0 ≠ 0 ∨ tangent q φ 1 ≠ 0 := by
  by_contra hn
  push Not at hn
  have hfirst (i : Fin 2) : PowerSeries.coeff 1 (coordinate q φ i) = 0 := by
    fin_cases i
    · exact hn.1
    · exact hn.2
  have hle : Ideal.span (Set.range (coordinate q φ)) ≤
      Ideal.span {(PowerSeries.X : PowerSeries K) ^ 2} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change coordinate q φ i ∈ (Ideal.span {(PowerSeries.X : PowerSeries K) ^ 2} :
      Ideal (PowerSeries K))
    apply Ideal.mem_span_singleton.mpr
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro m hm
    interval_cases m
    · simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using coordinate_constantCoeff q φ hφ i
    · exact hfirst i
  have hx : (PowerSeries.X : PowerSeries K) ∈ Ideal.span (Set.range (coordinate q φ)) := by
    rw [coordinate_span q φ hφ, PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hc := PowerSeries.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp (hle hx)) 1 (by decide)
  simp only [PowerSeries.coeff_one_X, one_ne_zero] at hc

private theorem second_coefficient_mul (f g : PowerSeries K)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 2 (f * g) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 g := by
  have hdiag : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
  simp [PowerSeries.coeff_mul, hdiag, PowerSeries.coeff_zero_eq_constantCoeff, hf, hg]

/-- The actual second coefficient of the original quadratic relation gives original-field isotropy. -/
theorem tangent_isotropic (hφ : Function.Surjective φ) :
    q.value (tangent q φ 0) (tangent q φ 1) = 0 := by
  have hq : (Ideal.Quotient.mk (Ideal.span {q.series})) q.series = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have h := congrArg φ hq
  have hC (a : K) : φ (Ideal.Quotient.mk _ (MvPowerSeries.C a)) = PowerSeries.C a :=
    φ.commutes a
  change φ (Ideal.Quotient.mk _
    (MvPowerSeries.C q.a0 * MvPowerSeries.X 0 ^ 2 +
      MvPowerSeries.C q.a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1 +
      MvPowerSeries.C q.a2 * MvPowerSeries.X 1 ^ 2)) = φ 0 at h
  simp only [map_add, map_mul, map_pow, hC, map_zero] at h
  change PowerSeries.C q.a0 * coordinate q φ 0 ^ 2 +
    PowerSeries.C q.a1 * coordinate q φ 0 * coordinate q φ 1 +
    PowerSeries.C q.a2 * coordinate q φ 1 ^ 2 = 0 at h
  have hc := congrArg (PowerSeries.coeff 2) h
  simp only [map_add, map_zero, pow_two, mul_assoc, PowerSeries.coeff_C_mul] at hc
  rw [second_coefficient_mul _ _ (coordinate_constantCoeff q φ hφ 0)
      (coordinate_constantCoeff q φ hφ 0),
    second_coefficient_mul _ _ (coordinate_constantCoeff q φ hφ 0)
      (coordinate_constantCoeff q φ hφ 1),
    second_coefficient_mul _ _ (coordinate_constantCoeff q φ hφ 1)
      (coordinate_constantCoeff q φ hφ 1)] at hc
  simpa only [Quadratic.value, tangent, pow_two, mul_assoc] using hc

/-- A genuine original-field smooth branch INTERNALLY splits the SAME original quadratic quotient. -/
def quotientEquiv (hφ : Function.Surjective φ) :
    QuadraticNode q ≃ₐ[K] NodeFlatPresentation.SplitNode K :=
  NodeFieldIsotropicQuadratic.quotientEquiv q (tangent q φ 0) (tangent q φ 1)
    (tangent_isotropic q φ hφ) (tangent_nonzero q φ hφ)

end Hironaka.Algebra.NodeFieldSmoothBranch
