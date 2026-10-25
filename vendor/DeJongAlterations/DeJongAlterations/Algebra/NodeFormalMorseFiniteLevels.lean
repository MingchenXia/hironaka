import DeJongAlterations.Algebra.NodeFormalMorseIterationNaturality
import DeJongAlterations.Algebra.NodeFormalMorseCoefficientLimit

/-!
# Canonically constructed compatible finite-level split-node normal forms

Both actual automorphisms and their actual inverses commute with every literal
coefficient reduction. No compatible family is an input: the family is the
deterministic iteration of the original error over each actual quotient.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- The image of the original ideal in the actual finite coefficient quotient. -/
def quotientBaseIdeal (I : Ideal R) (N : ℕ) : Ideal (R ⧸ I ^ N) :=
  I.map (Ideal.Quotient.mk (I ^ N))

/-- Its original `N`th power is actually zero, including the zero ring at `N=0`. -/
theorem quotientBaseIdeal_pow (I : Ideal R) (N : ℕ) : quotientBaseIdeal I N ^ N = 0 := by
  unfold quotientBaseIdeal
  rw [← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

theorem quotientBaseIdeal_isNilpotent (I : Ideal R) (N : ℕ) :
    IsNilpotent (quotientBaseIdeal I N) := ⟨N, quotientBaseIdeal_pow I N⟩

theorem quotientBaseError_mem (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    ∀ d, coeff d (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) ∈ quotientBaseIdeal I N := by
  intro d
  rw [coeff_map]
  exact Ideal.mem_map_of_mem _ (hH d)

/-- Exactly `N` deterministic native-substitution steps over the actual coefficient quotient. -/
def finiteState (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    IterationState (quotientBaseIdeal I N) :=
  iteration (quotientBaseIdeal I N) (quotientBaseIdeal_isNilpotent I N)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) (quotientBaseError_mem I H hH N) N

theorem finiteState_error_zero (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) : (finiteState I H hH N).error = 0 :=
  iteration_error_zero _ _ _ _ N (quotientBaseIdeal_pow I N)

/-- Each actual finite map has an exact constant smoothing parameter. -/
theorem finiteState_equation (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    (finiteState I H hH N).equiv
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (X 0 * X 1 - H)) =
        X 0 * X 1 - C (finiteState I H hH N).scalar := by
  have he := iteration_equation (quotientBaseIdeal I N) (quotientBaseIdeal_isNilpotent I N)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) (quotientBaseError_mem I H hH N) N
  change (finiteState I H hH N).equiv (_ - _) = _ - _ - (finiteState I H hH N).error at he
  rw [finiteState_error_zero, sub_zero] at he
  simpa only [finiteState, map_sub, map_mul, MvPowerSeries.map_X] using he

/-- All finite scalar parameters, forward maps, and inverse maps are actually compatible. -/
theorem finiteState_compatible (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow I hMN (finiteState I H hH N).scalar = (finiteState I H hH M).scalar ∧
      (∀ g, MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) ((finiteState I H hH N).equiv g) =
        (finiteState I H hH M).equiv (MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) g)) ∧
      (∀ g, MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) ((finiteState I H hH N).equiv.symm g) =
        (finiteState I H hH M).equiv.symm (MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) g)) := by
  let f := Ideal.Quotient.factorPow I hMN
  have he : MvPowerSeries.map f (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) =
      MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H := by
    ext d
    simp [f, coeff_map]
  have hn := iteration_map f (quotientBaseIdeal I N) (quotientBaseIdeal I M)
    (quotientBaseIdeal_isNilpotent I N) (quotientBaseIdeal_isNilpotent I M)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H)
    (quotientBaseError_mem I H hH N) (quotientBaseError_mem I H hH M) he N
  have hs := iteration_stable (quotientBaseIdeal I M) (quotientBaseIdeal_isNilpotent I M)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H) (quotientBaseError_mem I H hH M)
    M (N - M) (finiteState_error_zero I H hH M)
  have hsc : (iteration (quotientBaseIdeal I M) (quotientBaseIdeal_isNilpotent I M)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H) (quotientBaseError_mem I H hH M) N).scalar =
      (finiteState I H hH M).scalar := by
    simpa only [Nat.add_sub_of_le hMN, finiteState] using hs.2.1
  have hse : (iteration (quotientBaseIdeal I M) (quotientBaseIdeal_isNilpotent I M)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H) (quotientBaseError_mem I H hH M) N).equiv =
      (finiteState I H hH M).equiv := by
    simpa only [Nat.add_sub_of_le hMN, finiteState] using hs.2.2
  refine ⟨hn.1.trans hsc, ?_, ?_⟩
  · intro g
    exact (hn.2.2 g).trans (congrArg (fun e => e (MvPowerSeries.map f g)) hse)
  · intro g
    have hi := iteration_symm_map f (quotientBaseIdeal I N) (quotientBaseIdeal I M)
      (quotientBaseIdeal_isNilpotent I N) (quotientBaseIdeal_isNilpotent I M)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H)
      (quotientBaseError_mem I H hH N) (quotientBaseError_mem I H hH M) he N g
    rw [hse] at hi
    exact hi

/-- The finite scalar at the original first quotient vanishes internally. -/
theorem finiteState_one_scalar (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) :
    (finiteState I H hH 1).scalar = 0 := by
  have hz : MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H = 0 := by
    ext d
    rw [coeff_map, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [pow_one] using hH d)
  have hs := iteration_stable (quotientBaseIdeal I 1) (quotientBaseIdeal_isNilpotent I 1)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H) (quotientBaseError_mem I H hH 1) 0 1 hz
  exact hs.2.1

/-- The actual first finite map is the identity, not merely pointwise equal on variables. -/
theorem finiteState_one_equiv (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) :
    (finiteState I H hH 1).equiv = AlgEquiv.refl := by
  have hz : MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H = 0 := by
    ext d
    rw [coeff_map, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [pow_one] using hH d)
  have hs := iteration_stable (quotientBaseIdeal I 1) (quotientBaseIdeal_isNilpotent I 1)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H) (quotientBaseError_mem I H hH 1) 0 1 hz
  exact hs.2.2

end DeJongAlterations.Algebra.NodeFormalMorse
