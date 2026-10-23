import DeJongAlterations.Algebra.NodeFormalMorseNaturality

/-!
# Internally constructed finite Morse iteration

Every coordinate map and inverse is constructed from the original error.
The state records only the internally computed order and actual data; no
normal-form equation, compatible family, or automorphism is an input to the
iteration from the original error.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R]

/-- Actual finite correction data, including its proved coefficient error order. -/
structure IterationState (J : Ideal R) where
  order : ℕ
  order_ne_zero : order ≠ 0
  scalar : R
  error : Series R
  error_mem : ∀ d, coeff d error ∈ J ^ order
  equiv : Series R ≃ₐ[R] Series R

/-- One internally constructed doubled-order step. -/
def iterationStep (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J) : IterationState J where
  order := 2 * s.order
  order_ne_zero := Nat.mul_ne_zero (by decide) s.order_ne_zero
  scalar := s.scalar + correctedConstant (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem
  error := correctedResidual (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem
  error_mem := by
    simpa only [← pow_mul, Nat.mul_comm s.order 2] using
      correctedResidual_coeff_mem (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem
  equiv := s.equiv.trans
    (correctionEquiv (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem).symm

/-- The canonical finite iteration from the original error and original coefficient ideal. -/
def iteration (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) : ℕ → IterationState J
  | 0 => {
    order := 1
    order_ne_zero := by decide
    scalar := 0
    error := H
    error_mem := by simpa only [pow_one] using hH
    equiv := AlgEquiv.refl }
  | k + 1 => iterationStep J hJ (iteration J hJ H hH k)

/-- The computed exponent is exactly the doubled order `2^k`. -/
theorem iteration_order (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k : ℕ) : (iteration J hJ H hH k).order = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * (iteration J hJ H hH k).order = 2 ^ (k + 1)
    rw [ih, pow_succ, Nat.mul_comm]

/-- Every finite state has the exact actual transformed equation. -/
theorem iteration_equation (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k : ℕ) :
    (iteration J hJ H hH k).equiv (X 0 * X 1 - H) =
      X 0 * X 1 - C (iteration J hJ H hH k).scalar - (iteration J hJ H hH k).error := by
  induction k with
  | zero => simp [iteration]
  | succ k ih =>
    change (correctionEquiv (J ^ (iteration J hJ H hH k).order)
        (hJ.pow_of_pos (iteration J hJ H hH k).order_ne_zero)
        (iteration J hJ H hH k).error (iteration J hJ H hH k).error_mem).symm
      ((iteration J hJ H hH k).equiv (X 0 * X 1 - H)) = _
    rw [ih]
    exact correctionEquation_with_constant _ _ _ _ _

/-- The actual residual error has precisely the proved doubled coefficient order. -/
theorem iteration_error_coeff_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k : ℕ) :
    ∀ d, coeff d (iteration J hJ H hH k).error ∈ J ^ (2 ^ k) := by
  simpa only [iteration_order] using (iteration J hJ H hH k).error_mem

theorem iterationStep_error_of_zero (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J)
    (hs : s.error = 0) : (iterationStep J hJ s).error = 0 := by
  have haux (E : Series R) (hE : ∀ d, coeff d E ∈ J ^ s.order) (he : E = 0) :
      correctedResidual (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) E hE = 0 := by
    subst E
    exact correctedResidual_zero _ _ _
  exact haux s.error s.error_mem hs

theorem iterationStep_scalar_of_zero (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J)
    (hs : s.error = 0) : (iterationStep J hJ s).scalar = s.scalar := by
  simp [iterationStep, hs]

theorem iterationStep_equiv_of_zero (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J)
    (hs : s.error = 0) : (iterationStep J hJ s).equiv = s.equiv := by
  simp [iterationStep, hs, correctionEquiv_zero]
  apply AlgEquiv.ext
  intro f
  rfl

/-- All actual data stabilize after the error vanishes, despite the unused order continuing to double. -/
theorem iteration_stable (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k l : ℕ) (hk : (iteration J hJ H hH k).error = 0) :
    (iteration J hJ H hH (k + l)).error = 0 ∧
      (iteration J hJ H hH (k + l)).scalar = (iteration J hJ H hH k).scalar ∧
      (iteration J hJ H hH (k + l)).equiv = (iteration J hJ H hH k).equiv := by
  induction l with
  | zero => exact ⟨hk, rfl, rfl⟩
  | succ l ih =>
    change (iterationStep J hJ (iteration J hJ H hH (k + l))).error = 0 ∧
      (iterationStep J hJ (iteration J hJ H hH (k + l))).scalar = _ ∧
      (iterationStep J hJ (iteration J hJ H hH (k + l))).equiv = _
    exact ⟨iterationStep_error_of_zero J hJ _ ih.1,
      (iterationStep_scalar_of_zero J hJ _ ih.1).trans ih.2.1,
      (iterationStep_equiv_of_zero J hJ _ ih.1).trans ih.2.2⟩

/-- A nilpotent ideal power kills the actual residual once its internally computed order is large enough. -/
theorem iteration_error_zero_of_pow (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (N k : ℕ) (hN : J ^ N = 0) (hk : N ≤ 2 ^ k) :
    (iteration J hJ H hH k).error = 0 := by
  ext d
  have hd := Ideal.pow_le_pow_right hk (iteration_error_coeff_mem J hJ H hH k d)
  rw [hN] at hd
  simpa only [Ideal.zero_eq_bot, Ideal.mem_bot, map_zero] using hd

/-- In particular `N` steps suffice when the actual `N`th ideal power is zero. -/
theorem iteration_error_zero (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (N : ℕ) (hN : J ^ N = 0) :
    (iteration J hJ H hH N).error = 0 :=
  iteration_error_zero_of_pow J hJ H hH N N hN (Nat.le_of_lt N.lt_two_pow_self)

end DeJongAlterations.Algebra.NodeFormalMorse
