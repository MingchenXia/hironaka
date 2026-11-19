import Hironaka.Algebra.NodeNonsplitNaturality
import Hironaka.Algebra.NodeFormalMorseIteration

/-!
# Internally constructed finite Morse iteration Q

Every coordinate map and inverse is constructed from the original error.
The state records only the internally computed order and actual data; no
normal-form equation, compatible family, or automorphism is an input to the
iteration from the original error.
-/

noncomputable section

namespace Hironaka.Algebra.NodeNonsplit

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] (Q : Quadratic R)

/-- One internally constructed doubled-order step. -/
def iterationStep (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J) : IterationState J where
  order := 2 * s.order
  order_ne_zero := Nat.mul_ne_zero (by decide) s.order_ne_zero
  scalar := s.scalar + correctedConstant Q (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem
  error := correctedResidual Q (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem
  error_mem := by
    simpa only [← pow_mul, Nat.mul_comm s.order 2] using
      correctedResidual_coeff_mem Q (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem
  equiv := s.equiv.trans
    (correctionEquiv Q (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem).symm

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
  | k + 1 => iterationStep Q J hJ (iteration J hJ H hH k)

/-- The computed exponent is exactly the doubled order `2^k`. -/
theorem iteration_order (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k : ℕ) : (iteration Q J hJ H hH k).order = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * (iteration Q J hJ H hH k).order = 2 ^ (k + 1)
    rw [ih, pow_succ, Nat.mul_comm]

/-- Every finite state has the exact actual transformed equation. -/
theorem iteration_equation (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k : ℕ) :
    (iteration Q J hJ H hH k).equiv (Q.series - H) =
      Q.series - C (iteration Q J hJ H hH k).scalar - (iteration Q J hJ H hH k).error := by
  induction k with
  | zero => simp [iteration]
  | succ k ih =>
    change (correctionEquiv Q (J ^ (iteration Q J hJ H hH k).order)
        (hJ.pow_of_pos (iteration Q J hJ H hH k).order_ne_zero)
        (iteration Q J hJ H hH k).error (iteration Q J hJ H hH k).error_mem).symm
      ((iteration Q J hJ H hH k).equiv (Q.series - H)) = _
    rw [ih]
    exact correctionEquation_with_constant Q _ _ _ _ _

/-- The actual residual error has precisely the proved doubled coefficient order. -/
theorem iteration_error_coeff_mem (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k : ℕ) :
    ∀ d, coeff d (iteration Q J hJ H hH k).error ∈ J ^ (2 ^ k) := by
  simpa only [iteration_order Q] using (iteration Q J hJ H hH k).error_mem

theorem iterationStep_error_of_zero (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J)
    (hs : s.error = 0) : (iterationStep Q J hJ s).error = 0 := by
  have haux (E : Series R) (hE : ∀ d, coeff d E ∈ J ^ s.order) (he : E = 0) :
      correctedResidual Q (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) E hE = 0 := by
    subst E
    exact correctedResidual_zero Q _ _ _
  exact haux s.error s.error_mem hs

theorem iterationStep_scalar_of_zero (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J)
    (hs : s.error = 0) : (iterationStep Q J hJ s).scalar = s.scalar := by
  simp [iterationStep, hs]

theorem iterationStep_equiv_of_zero (J : Ideal R) (hJ : IsNilpotent J) (s : IterationState J)
    (hs : s.error = 0) : (iterationStep Q J hJ s).equiv = s.equiv := by
  simp [iterationStep, hs, correctionEquiv_zero Q]
  apply AlgEquiv.ext
  intro f
  rfl

/-- All actual data stabilize after the error vanishes, despite the unused order continuing to double. -/
theorem iteration_stable (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (k l : ℕ) (hk : (iteration Q J hJ H hH k).error = 0) :
    (iteration Q J hJ H hH (k + l)).error = 0 ∧
      (iteration Q J hJ H hH (k + l)).scalar = (iteration Q J hJ H hH k).scalar ∧
      (iteration Q J hJ H hH (k + l)).equiv = (iteration Q J hJ H hH k).equiv := by
  induction l with
  | zero => exact ⟨hk, rfl, rfl⟩
  | succ l ih =>
    change (iterationStep Q J hJ (iteration Q J hJ H hH (k + l))).error = 0 ∧
      (iterationStep Q J hJ (iteration Q J hJ H hH (k + l))).scalar = _ ∧
      (iterationStep Q J hJ (iteration Q J hJ H hH (k + l))).equiv = _
    exact ⟨iterationStep_error_of_zero Q J hJ _ ih.1,
      (iterationStep_scalar_of_zero Q J hJ _ ih.1).trans ih.2.1,
      (iterationStep_equiv_of_zero Q J hJ _ ih.1).trans ih.2.2⟩

/-- A nilpotent ideal power kills the actual residual once its internally computed order is large enough. -/
theorem iteration_error_zero_of_pow (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (N k : ℕ) (hN : J ^ N = 0) (hk : N ≤ 2 ^ k) :
    (iteration Q J hJ H hH k).error = 0 := by
  ext d
  have hd := Ideal.pow_le_pow_right hk (iteration_error_coeff_mem Q J hJ H hH k d)
  rw [hN] at hd
  simpa only [Ideal.zero_eq_bot, Ideal.mem_bot, map_zero] using hd

/-- In particular `N` steps suffice when the actual `N`th ideal power is zero. -/
theorem iteration_error_zero (J : Ideal R) (hJ : IsNilpotent J) (H : Series R)
    (hH : ∀ d, coeff d H ∈ J) (N : ℕ) (hN : J ^ N = 0) :
    (iteration Q J hJ H hH N).error = 0 :=
  iteration_error_zero_of_pow Q J hJ H hH N N hN (Nat.le_of_lt N.lt_two_pow_self)

end Hironaka.Algebra.NodeNonsplit
