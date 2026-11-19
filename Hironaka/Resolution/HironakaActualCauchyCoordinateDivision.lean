import Hironaka.Analytic.LastVariableTaylorDivision
import Hironaka.Analytic.HolomorphicTaylorTail

/-!
# Actual coordinate Cauchy division on one fixed supremum-norm polydisc

These operators are genuine Cauchy integrals and Taylor quotients. Their
holomorphicity and sup-norm bounds are produced from the existing analytic
Cauchy theorems, with no caller-supplied division or bounded-operator premise.
The full multigenerator diagram partition and canonical convergence are separate.
-/

set_option autoImplicit false
open Set Metric
open scoped Topology

namespace Hironaka.HironakaActualCauchyCoordinateDivision

noncomputable section

variable {n : ℕ}

abbrev CoordinateSpace (n : ℕ) := Fin n → ℂ

/-- The actual continuous-linear insertion of one complex coordinate. -/
def coordinateInsert (i : Fin n) : CoordinateSpace n × ℂ →L[ℂ] CoordinateSpace n :=
  ContinuousLinearMap.pi fun j =>
    if j = i then ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ
    else (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ)

theorem coordinateInsert_apply (i j : Fin n) (z : CoordinateSpace n) (t : ℂ) :
    coordinateInsert i (z,t) j = if j = i then t else z j := by
  simp only [coordinateInsert, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem coordinateInsert_self (i : Fin n) (z : CoordinateSpace n) :
    coordinateInsert i (z,z i) = z := by
  ext j
  rw [coordinateInsert_apply]
  split_ifs with hj
  · exact congrArg z hj.symm
  · rfl

theorem coordinateInsert_override (i : Fin n) (z : CoordinateSpace n) (t u : ℂ) :
    coordinateInsert i (coordinateInsert i (z,t),u) = coordinateInsert i (z,u) := by
  ext j
  by_cases hj : j = i <;> simp [coordinateInsert_apply,hj]

/-- Coordinate insertion preserves the entire unchanged open polydisc. -/
theorem coordinateInsert_mem_ball (i : Fin n) {R : ℝ} (hR : 0 < R)
    {z : CoordinateSpace n} (hz : z ∈ ball 0 R) {t : ℂ} (ht : t ∈ ball 0 R) :
    coordinateInsert i (z,t) ∈ ball 0 R := by
  rw [mem_ball_zero_iff] at hz ht ⊢
  apply (pi_norm_lt_iff hR).mpr
  intro j
  rw [coordinateInsert_apply]
  split_ifs with hj
  · exact ht
  · exact (norm_le_pi_norm z j).trans_lt hz

def coordinateSlice (h : CoordinateSpace n → ℂ) (i : Fin n) :
    CoordinateSpace n × ℂ → ℂ := h ∘ coordinateInsert i

def coordinateCoeff (h : CoordinateSpace n → ℂ) (i : Fin n)
    (ρ : ℝ) (k : ℕ) : CoordinateSpace n → ℂ :=
  lastCoeff (coordinateSlice h i) ρ k

def coordinateQuot (h : CoordinateSpace n → ℂ) (i : Fin n)
    (ρ : ℝ) (d : ℕ) (z : CoordinateSpace n) : ℂ :=
  lastQuot (coordinateSlice h i) ρ d (z,z i)

def coordinateLow (h : CoordinateSpace n → ℂ) (i : Fin n)
    (ρ : ℝ) (d : ℕ) (z : CoordinateSpace n) : ℂ :=
  ∑ k ∈ Finset.range d, coordinateCoeff h i ρ k z * z i ^ k

/-- The actual coefficient functions are independent of the replaced coordinate. -/
theorem coordinateCoeff_insert (h : CoordinateSpace n → ℂ) (i : Fin n)
    (ρ : ℝ) (k : ℕ) (z : CoordinateSpace n) (t : ℂ) :
    coordinateCoeff h i ρ k (coordinateInsert i (z,t)) = coordinateCoeff h i ρ k z := by
  simp only [coordinateCoeff,lastCoeff,coordinateSlice,Function.comp_apply,
    coordinateInsert_override]

/-- Along its actual coordinate line the low operator is literally a finite polynomial. -/
theorem coordinateLow_insert (h : CoordinateSpace n → ℂ) (i : Fin n)
    (ρ : ℝ) (d : ℕ) (z : CoordinateSpace n) (t : ℂ) :
    coordinateLow h i ρ d (coordinateInsert i (z,t)) =
      ∑ j ∈ Finset.range d, coordinateCoeff h i ρ j z * t ^ j := by
  simp only [coordinateLow,coordinateCoeff_insert,coordinateInsert_apply,ite_true]

private theorem coordinateSlice_differentiableOn {h : CoordinateSpace n → ℂ}
    {R : ℝ} (hR : 0 < R) (hh : DifferentiableOn ℂ h (ball 0 R)) (i : Fin n) :
    DifferentiableOn ℂ (coordinateSlice h i) (ball 0 R ×ˢ ball 0 R) :=
  hh.comp (coordinateInsert i).differentiable.differentiableOn
    (fun _ hx => coordinateInsert_mem_ball i hR hx.1 hx.2)

theorem coordinateCoeff_differentiableOn {h : CoordinateSpace n → ℂ}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (i : Fin n) (k : ℕ) :
    DifferentiableOn ℂ (coordinateCoeff h i ρ k) (ball 0 R) :=
  differentiableOn_lastCoeff hρ hρR
    (coordinateSlice_differentiableOn (hρ.trans hρR) hh i) k

/-- The concrete Cauchy quotient is holomorphic on the whole original polydisc. -/
theorem coordinateQuot_differentiableOn {h : CoordinateSpace n → ℂ}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (i : Fin n) (d : ℕ) :
    DifferentiableOn ℂ (coordinateQuot h i ρ d) (ball 0 R) := by
  have hQ := differentiableOn_lastQuot hρ hρR
    (coordinateSlice_differentiableOn (hρ.trans hρR) hh i) d
  have hgraph : Differentiable ℂ (fun z : CoordinateSpace n => (z,z i)) :=
    differentiable_id.prodMk
      (ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable
  exact hQ.comp hgraph.differentiableOn (fun z hz =>
    ⟨hz,mem_ball_zero_iff.mpr ((norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.mp hz))⟩)

/-- The actual low-coordinate Taylor polynomial is holomorphic on that same domain. -/
theorem coordinateLow_differentiableOn {h : CoordinateSpace n → ℂ}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (i : Fin n) (d : ℕ) :
    DifferentiableOn ℂ (coordinateLow h i ρ d) (ball 0 R) := by
  apply DifferentiableOn.fun_sum
  intro k _hk
  exact (coordinateCoeff_differentiableOn hρ hρR hh i k).fun_mul
    ((ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable.differentiableOn.pow k)

/-- This identity uses the independently constructed actual Cauchy quotient. -/
theorem coordinate_division_identity {h : CoordinateSpace n → ℂ}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (i : Fin n) (d : ℕ)
    {z : CoordinateSpace n} (hz : z ∈ ball 0 R) :
    h z = coordinateQuot h i ρ d z * z i ^ d + coordinateLow h i ρ d z := by
  have hzi : z i ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr ((norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.mp hz))
  have he := eq_lastQuot_mul_add hρ hρR
    (coordinateSlice_differentiableOn (hρ.trans hρR) hh i) d (z,z i) ⟨hz,hzi⟩
  simpa only [coordinateSlice,Function.comp_apply,coordinateInsert_self,
    coordinateQuot,coordinateLow,coordinateCoeff] using he

/-- Genuine Cauchy coefficients, rather than an assumed formal support predicate,
give the exact low-coordinate coefficient projection. -/
theorem coordinateCoeff_low {h : CoordinateSpace n → ℂ}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (i : Fin n) (d k : ℕ)
    {z : CoordinateSpace n} (hz : z ∈ ball 0 R) :
    coordinateCoeff (coordinateLow h i ρ d) i ρ k z =
      if k < d then coordinateCoeff h i ρ k z else 0 := by
  have hlow := coordinateLow_differentiableOn hρ hρR hh i d
  have hslice := coordinateSlice_differentiableOn (hρ.trans hρR) hlow i
  have he : (fun t : ℂ => coordinateSlice (coordinateLow h i ρ d) i (z,t)) =
      fun t => ∑ j ∈ Finset.range d, coordinateCoeff h i ρ j z * t ^ j := by
    funext t
    exact coordinateLow_insert h i ρ d z t
  change lastCoeff (coordinateSlice (coordinateLow h i ρ d) i) ρ k z = _
  rw [HolomorphicTaylorTail.lastCoeff_eq_iteratedDeriv hρ hρR hslice k hz,he]
  rw [iteratedDeriv_fun_sum (fun j _hj =>
    (contDiff_const.mul (contDiff_id.pow j)).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]
  have hsum : (∑ j ∈ Finset.range d, coordinateCoeff h i ρ j z *
      ((if k = j then j.factorial else 0 : ℕ) : ℂ)) =
      if k < d then coordinateCoeff h i ρ k z * (k.factorial : ℂ) else 0 := by
    by_cases hk : k < d
    · rw [if_pos hk,Finset.sum_eq_single k]
      · simp only [ite_true]
      · intro j _hj hjk
        simp only [if_neg (Ne.symm hjk),Nat.cast_zero,mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hk)).elim
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro j hj
      have hkj : k ≠ j := by
        intro heq
        subst j
        exact hk (Finset.mem_range.mp hj)
      simp only [if_neg hkj,Nat.cast_zero,mul_zero]
  rw [hsum]
  by_cases hk : k < d
  · rw [if_pos hk,if_pos hk]
    have hfact : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  · rw [if_neg hk,if_neg hk,mul_zero]

/-- Concrete actual Cauchy quotient and truncation bounds apply on the unchanged
polydisc to every bounded holomorphic input, before any Neumann iteration. -/
theorem exists_coordinate_division_bounds (i : Fin n) (d : ℕ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ Cq Ct : ℝ, 0 ≤ Cq ∧ 0 ≤ Ct ∧
      Ct = ∑ k ∈ Finset.range d, (R / ρ) ^ k ∧
      ∀ (M : ℝ) (h : CoordinateSpace n → ℂ),
        DifferentiableOn ℂ h (ball 0 R) →
        (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
        ∀ z ∈ ball (0 : CoordinateSpace n) R,
          ‖coordinateQuot h i ρ d z‖ ≤ Cq * M ∧
          ‖coordinateLow h i ρ d z‖ ≤ Ct * M := by
  have hR : 0 < R := hρ.trans hρR
  obtain ⟨Cq,hCq,hQ⟩ := exists_norm_lastQuot_le (E := CoordinateSpace n) d hρ hρR
  refine ⟨Cq,∑ k ∈ Finset.range d,(R / ρ)^k,hCq,?_,rfl,?_⟩
  · exact Finset.sum_nonneg fun _ _ => by positivity
  intro M h hh hM z hz
  have hM0 : 0 ≤ M := (norm_nonneg (h 0)).trans (hM 0 (mem_ball_self hR))
  have hslice := coordinateSlice_differentiableOn (hρ.trans hρR) hh i
  have hbound : ∀ p ∈ ball (0 : CoordinateSpace n) R ×ˢ ball (0 : ℂ) R,
      ‖coordinateSlice h i p‖ ≤ M :=
    fun p hp => hM _ (coordinateInsert_mem_ball i (hρ.trans hρR) hp.1 hp.2)
  have hzi : ‖z i‖ ≤ R := (norm_le_pi_norm z i).trans
    (mem_ball_zero_iff.mp hz).le
  refine ⟨hQ R M (coordinateSlice h i) hslice hbound (z,z i)
    ⟨hz,mem_ball_zero_iff.mpr ((norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.mp hz))⟩,?_⟩
  change ‖∑ k ∈ Finset.range d, coordinateCoeff h i ρ k z * z i ^ k‖ ≤ _
  calc
    _ ≤ ∑ k ∈ Finset.range d, ‖coordinateCoeff h i ρ k z * z i ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range d, M / ρ ^ k * R ^ k := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [norm_mul,norm_pow]
      exact mul_le_mul (norm_lastCoeff_le hρ hρR hslice hbound k z hz)
        (pow_le_pow_left₀ (norm_nonneg _) hzi k) (by positivity) (by positivity)
    _ = (∑ k ∈ Finset.range d, (R / ρ) ^ k) * M := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [div_pow]
      ring

end

end Hironaka.HironakaActualCauchyCoordinateDivision
