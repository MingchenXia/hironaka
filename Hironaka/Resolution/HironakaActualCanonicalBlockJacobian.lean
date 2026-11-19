import Hironaka.Resolution.HironakaActualRelativeStandardnessBlockSupport
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finset.Max

/-!
# Internally selected derivatives of the same canonical family

Every actual degree-prefix essential block has a nonzero actual Jacobian.
Only the original ideal, its actual monomial order, and the cutoff are inputs.
The vertex choice is fixed independently of cutoffs. This is the Jacobian
part of BM97(7.2)(4); membership in a coordinate ideal or an adapted flag is
not asserted. The genuine higher derivatives are constructed from their
entire coefficients and proved to satisfy the actual partial-derivative
recursion. No convergence or prescribed rank/basis is an input.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualCanonicalBlockJacobian

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualRelativeStandardnessBlockSupport

variable {n : ℕ}

/-- The actual product of natural coordinate factorials, in the genuine field. -/
def actualExponentFactorial (α : Fin n →₀ ℕ) : ℂ :=
  ∏ i : Fin n, ((α i).factorial : ℂ)

theorem actualExponentFactorial_ne_zero (α : Fin n →₀ ℕ) :
    actualExponentFactorial α ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (α i)

private theorem actualExponentFactorial_zero : actualExponentFactorial (0 : Fin n →₀ ℕ) = 1 := by
  simp [actualExponentFactorial]

private theorem actualExponentFactorial_single (i : Fin n) :
    actualExponentFactorial (Finsupp.single i 1) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  by_cases hj : j = i
  · subst j
    simp
  · simp [Finsupp.single_eq_of_ne hj]

private theorem actualExponentFactorial_add_single (α : Fin n →₀ ℕ) (i : Fin n) :
    actualExponentFactorial (α + Finsupp.single i 1) =
      actualExponentFactorial α * ((α i + 1 : ℕ) : ℂ) := by
  have h (j : Fin n) :
      ((((α + Finsupp.single i 1 : Fin n →₀ ℕ) j)).factorial : ℂ) =
        ((α j).factorial : ℂ) * (if j = i then ((α i + 1 : ℕ) : ℂ) else 1) := by
    by_cases hj : j = i
    · subst j
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, ite_true,
        Nat.factorial_succ, Nat.cast_mul]
      ring
    · simp [Finsupp.single_eq_of_ne hj, hj]
  simp only [actualExponentFactorial, h, Finset.prod_mul_distrib]
  simp

/-- The entire genuine formal higher derivative, with no truncated-series surrogate. -/
def actualFormalMultiDerivative (β : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries (Fin n) ℂ :=
  fun γ => MvPowerSeries.coeff (γ + β) F *
    (actualExponentFactorial (γ + β) / actualExponentFactorial γ)

theorem coeff_actualFormalMultiDerivative (β : Fin n →₀ ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (γ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff γ (actualFormalMultiDerivative β F) =
      MvPowerSeries.coeff (γ + β) F *
        (actualExponentFactorial (γ + β) / actualExponentFactorial γ) := rfl

/-- Zero actual derivatives retain the entire original member. -/
theorem actualFormalMultiDerivative_zero (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative 0 F = F := by
  apply MvPowerSeries.ext
  intro γ
  rw [coeff_actualFormalMultiDerivative, add_zero,
    div_self (actualExponentFactorial_ne_zero γ), mul_one]

/-- The defined higher derivative is a genuine composition of the actual partial derivatives. -/
theorem actualFormalMultiDerivative_add_single (β : Fin n →₀ ℕ)
    (i : Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative (β + Finsupp.single i 1) F =
      MvPowerSeries.pderiv ℂ i (actualFormalMultiDerivative β F) := by
  apply MvPowerSeries.ext
  intro γ
  rw [coeff_actualFormalMultiDerivative, MvPowerSeries.coeff_pderiv,
    coeff_actualFormalMultiDerivative]
  have he : γ + Finsupp.single i 1 + β = γ + (β + Finsupp.single i 1) := by
    ac_rfl
  rw [he, actualExponentFactorial_add_single]
  have hc : (((γ i + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (γ i)
  field_simp [actualExponentFactorial_ne_zero γ, hc]
  simp only [Nat.cast_add, Nat.cast_one]

/-- The actual constant derivative coefficient is the original coefficient times its factorial. -/
theorem constantCoeff_actualFormalMultiDerivative (β : Fin n →₀ ℕ)
    (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.constantCoeff (actualFormalMultiDerivative β F) =
      MvPowerSeries.coeff β F * actualExponentFactorial β := by
  change MvPowerSeries.coeff 0 (actualFormalMultiDerivative β F) = _
  rw [coeff_actualFormalMultiDerivative, zero_add, actualExponentFactorial_zero, div_one]

/-- Actual Jacobian entries retain the original coefficients at the exact successor exponent. -/
theorem constantCoeff_pderiv_actualFormalMultiDerivative (β : Fin n →₀ ℕ)
    (i : Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.constantCoeff
        (MvPowerSeries.pderiv ℂ i (actualFormalMultiDerivative β F)) =
      MvPowerSeries.coeff (β + Finsupp.single i 1) F *
        actualExponentFactorial (β + Finsupp.single i 1) := by
  rw [← actualFormalMultiDerivative_add_single, constantCoeff_actualFormalMultiDerivative]

/-- The variables actually occurring in at least one actual minimal vertex. -/
def actualCanonicalEssentialVariables (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) : Set (Fin n) :=
  {j | ∃ a : actualInitialVertices m K, a.val j ≠ 0}

private theorem exists_least_degree_actual_vertex (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    ∃ a : actualInitialVertices m K, a.val j.val ≠ 0 ∧
      ∀ b : actualInitialVertices m K, b.val j.val ≠ 0 →
        normalExponentDegree a.val ≤ normalExponentDegree b.val := by
  let s : Finset (actualInitialVertices m K) := Finset.univ.filter (fun a => a.val j.val ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := j.property
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image (fun a => normalExponentDegree a.val) hs
  exact ⟨a, (Finset.mem_filter.mp ha).2, fun b hb =>
    hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)⟩

/-- A fixed actual least-degree vertex, chosen once rather than separately at each cutoff. -/
def actualCanonicalDerivativeVertex (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    actualInitialVertices m K :=
  Classical.choose (exists_least_degree_actual_vertex m K j)

theorem actualCanonicalDerivativeVertex_spec (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    (actualCanonicalDerivativeVertex m K j).val j.val ≠ 0 ∧
      ∀ b : actualInitialVertices m K, b.val j.val ≠ 0 →
        normalExponentDegree (actualCanonicalDerivativeVertex m K j).val ≤
          normalExponentDegree b.val :=
  Classical.choose_spec (exists_least_degree_actual_vertex m K j)

/-- The literal selected derivative exponent; the subtracted coordinate is genuinely positive. -/
def actualCanonicalDerivativeExponent (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) : Fin n →₀ ℕ :=
  (actualCanonicalDerivativeVertex m K j).val - Finsupp.single j.val 1

theorem actualCanonicalDerivativeExponent_add_single (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    actualCanonicalDerivativeExponent m K j + Finsupp.single j.val 1 =
      (actualCanonicalDerivativeVertex m K j).val := by
  apply tsub_add_cancel_of_le
  intro i
  by_cases hi : i = j.val
  · subst i
    simpa only [Finsupp.single_eq_same] using
      Nat.one_le_iff_ne_zero.mpr (actualCanonicalDerivativeVertex_spec m K j).1
  · simp [Finsupp.single_eq_of_ne hi]

/-- The actual cutoff block embeds into the fixed essential-variable index type. -/
def actualCanonicalBlockEssentialVariable (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ)
    (j : actualDegreePrefixVariables m K k) : actualCanonicalEssentialVariables m K :=
  ⟨j.val, by obtain ⟨a, _, ha⟩ := j.property; exact ⟨a, ha⟩⟩

theorem actualCanonicalDerivativeVertex_degree_le (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (j : actualDegreePrefixVariables m K k) :
    normalExponentDegree (actualCanonicalDerivativeVertex m K
      (actualCanonicalBlockEssentialVariable m K k j)).val ≤ k := by
  obtain ⟨a, hak, haj⟩ := j.property
  exact ((actualCanonicalDerivativeVertex_spec m K
    (actualCanonicalBlockEssentialVariable m K k j)).2 a haj).trans hak

theorem actualCanonicalDerivativeExponent_support (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (j : actualDegreePrefixVariables m K k)
    (i : Fin n) (hi : i ∉ actualDegreePrefixVariables m K k) :
    actualCanonicalDerivativeExponent m K (actualCanonicalBlockEssentialVariable m K k j) i = 0 := by
  let a := actualCanonicalDerivativeVertex m K (actualCanonicalBlockEssentialVariable m K k j)
  have hai : a.val i = 0 := by
    by_contra hne
    exact hi ⟨a, actualCanonicalDerivativeVertex_degree_le m K k j, hne⟩
  change (a.val - Finsupp.single j.val 1 : Fin n →₀ ℕ) i = 0
  simp [Finsupp.tsub_apply, hai]

/-- The selected actual derivative of the SAME original canonical vertex member. -/
def actualCanonicalEssentialDerivative (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    MvPowerSeries (Fin n) ℂ :=
  actualFormalMultiDerivative (actualCanonicalDerivativeExponent m K j)
    (actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K j))

theorem actualCanonicalEssentialDerivative_constant_zero (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    MvPowerSeries.constantCoeff (actualCanonicalEssentialDerivative m K j) = 0 := by
  rw [actualCanonicalEssentialDerivative, constantCoeff_actualFormalMultiDerivative]
  have hle : actualCanonicalDerivativeExponent m K j ≤ (actualCanonicalDerivativeVertex m K j).val :=
    tsub_le_self
  have hne : actualCanonicalDerivativeExponent m K j ≠ (actualCanonicalDerivativeVertex m K j).val := by
    intro he
    have h := actualCanonicalDerivativeExponent_add_single m K j
    rw [he] at h
    have hz : Finsupp.single j.val 1 = 0 := add_eq_left.mp h
    have hc := congrArg (fun α : Fin n →₀ ℕ => α j.val) hz
    simp at hc
  have hlt := m.toSyn_strictMono (lt_of_le_of_ne hle hne)
  rw [actualReducedVertexSeries_coefficient_lower m K _ _ hlt, zero_mul]

theorem actualCanonicalEssentialDerivative_jacobian_diagonal (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ j.val
      (actualCanonicalEssentialDerivative m K j)) =
        actualExponentFactorial (actualCanonicalDerivativeVertex m K j).val := by
  rw [actualCanonicalEssentialDerivative, constantCoeff_pderiv_actualFormalMultiDerivative,
    actualCanonicalDerivativeExponent_add_single, actualReducedVertexSeries_coefficient, one_mul]

theorem actualCanonicalEssentialDerivative_jacobian_lower_coordinate (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K)
    (i : Fin n) (hi : m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single j.val 1)) :
    MvPowerSeries.constantCoeff
      (MvPowerSeries.pderiv ℂ i (actualCanonicalEssentialDerivative m K j)) = 0 := by
  rw [actualCanonicalEssentialDerivative, constantCoeff_pderiv_actualFormalMultiDerivative]
  have hlt : m.toSyn (actualCanonicalDerivativeExponent m K j + Finsupp.single i 1) <
      m.toSyn (actualCanonicalDerivativeVertex m K j).val := by
    rw [← actualCanonicalDerivativeExponent_add_single m K j, map_add, map_add]
    simpa only [add_comm] using add_lt_add_left hi (m.toSyn (actualCanonicalDerivativeExponent m K j))
  rw [actualReducedVertexSeries_coefficient_lower m K _ _ hlt, zero_mul]

/-- The literal block Jacobian, not a matrix supplied as a rank certificate. -/
def actualCanonicalBlockJacobian (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) :
    Matrix (actualDegreePrefixVariables m K k) (actualDegreePrefixVariables m K k) ℂ :=
  fun j i => MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i.val
    (actualCanonicalEssentialDerivative m K (actualCanonicalBlockEssentialVariable m K k j)))

/-- Its actual determinant is exactly the product of the internally selected vertex factorials. -/
theorem actualCanonicalBlockJacobian_det (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) :
    (actualCanonicalBlockJacobian m K k).det =
      ∏ j : actualDegreePrefixVariables m K k,
        actualExponentFactorial (actualCanonicalDerivativeVertex m K
          (actualCanonicalBlockEssentialVariable m K k j)).val := by
  have hinj : Function.Injective (fun j : actualDegreePrefixVariables m K k =>
      m.toSyn (Finsupp.single j.val 1)) := by
    intro i j hij
    apply Subtype.ext
    exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) (m.toSyn.injective hij)
  let ord : LinearOrder (actualDegreePrefixVariables m K k) :=
    LinearOrder.lift' (fun j => m.toSyn (Finsupp.single j.val 1)) hinj
  let : LinearOrder (actualDegreePrefixVariables m K k) := ord
  have htri : @Matrix.IsUpperTriangular (actualDegreePrefixVariables m K k) ℂ
      inferInstance ord.toLT (actualCanonicalBlockJacobian m K k) := by
    intro j i hij
    change m.toSyn (Finsupp.single i.val 1) < m.toSyn (Finsupp.single j.val 1) at hij
    exact actualCanonicalEssentialDerivative_jacobian_lower_coordinate m K
      (actualCanonicalBlockEssentialVariable m K k j) i.val hij
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_congr rfl
  intro j _
  exact actualCanonicalEssentialDerivative_jacobian_diagonal m K
    (actualCanonicalBlockEssentialVariable m K k j)

/-- ONLY the original ideal/order/cutoff internally produce every nonzero block Jacobian. -/
theorem actualCanonicalBlockJacobian_det_ne_zero (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) :
    (actualCanonicalBlockJacobian m K k).det ≠ 0 := by
  rw [actualCanonicalBlockJacobian_det]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => actualExponentFactorial_ne_zero _)

end

end Hironaka.HironakaActualCanonicalBlockJacobian
