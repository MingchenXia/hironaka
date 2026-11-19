import Hironaka.Algebra.NodeNonsplitIterationNaturality
import Hironaka.Algebra.NodeFormalMorseFiniteLevels
import Hironaka.Algebra.NodeFormalMorseCoefficientLimit

/-!
# Canonically constructed compatible finite-level quadratic normal forms

Both actual automorphisms and their actual inverses commute with every literal
coefficient reduction. No compatible family is an input: the family is the
deterministic iteration Q of the original error over each actual quotient.
-/

noncomputable section

namespace Hironaka.Algebra.NodeNonsplit

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] (Q : Quadratic R)

/-- Exactly `N` deterministic native-substitution steps over the actual coefficient quotient. -/
def finiteState (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    IterationState (quotientBaseIdeal I N) :=
  iteration (Q.map (Ideal.Quotient.mk (I ^ N))) (quotientBaseIdeal I N) (quotientBaseIdeal_isNilpotent I N)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) (quotientBaseError_mem I H hH N) N

theorem finiteState_error_zero (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) : (finiteState Q I H hH N).error = 0 :=
  iteration_error_zero (Q.map (Ideal.Quotient.mk (I ^ N))) _ _ _ _ N (quotientBaseIdeal_pow I N)

/-- Each actual finite map has an exact constant smoothing parameter. -/
theorem finiteState_equation (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    (finiteState Q I H hH N).equiv
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (Q.series - H)) =
        (Q.map (Ideal.Quotient.mk (I ^ N))).series - C (finiteState Q I H hH N).scalar := by
  have he := iteration_equation (Q.map (Ideal.Quotient.mk (I ^ N))) (quotientBaseIdeal I N) (quotientBaseIdeal_isNilpotent I N)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) (quotientBaseError_mem I H hH N) N
  change (finiteState Q I H hH N).equiv (_ - _) = _ - _ - (finiteState Q I H hH N).error at he
  rw [finiteState_error_zero Q, sub_zero] at he
  simpa only [finiteState, map_sub, Quadratic.map_series] using he

/-- All finite scalar parameters, forward maps, and inverse maps are actually compatible. -/
theorem finiteState_compatible (I : Ideal R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow I hMN (finiteState Q I H hH N).scalar = (finiteState Q I H hH M).scalar ∧
      (∀ g, MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) ((finiteState Q I H hH N).equiv g) =
        (finiteState Q I H hH M).equiv (MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) g)) ∧
      (∀ g, MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) ((finiteState Q I H hH N).equiv.symm g) =
        (finiteState Q I H hH M).equiv.symm (MvPowerSeries.map (Ideal.Quotient.factorPow I hMN) g)) := by
  let f := Ideal.Quotient.factorPow I hMN
  have he : MvPowerSeries.map f (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H) =
      MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H := by
    ext d
    simp [f, coeff_map]
  have hQ : (Q.map (Ideal.Quotient.mk (I ^ N))).map f = Q.map (Ideal.Quotient.mk (I ^ M)) := by
    rw [Quadratic.map_map]
    congr 1
  have hn := iteration_map (Q.map (Ideal.Quotient.mk (I ^ N))) f (quotientBaseIdeal I N) (quotientBaseIdeal I M)
    (quotientBaseIdeal_isNilpotent I N) (quotientBaseIdeal_isNilpotent I M)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H)
    (quotientBaseError_mem I H hH N) (quotientBaseError_mem I H hH M) he N
  rw [hQ] at hn
  have hs := iteration_stable (Q.map (Ideal.Quotient.mk (I ^ M))) (quotientBaseIdeal I M) (quotientBaseIdeal_isNilpotent I M)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H) (quotientBaseError_mem I H hH M)
    M (N - M) (finiteState_error_zero Q I H hH M)
  have hsc : (iteration (Q.map (Ideal.Quotient.mk (I ^ M))) (quotientBaseIdeal I M) (quotientBaseIdeal_isNilpotent I M)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H) (quotientBaseError_mem I H hH M) N).scalar =
      (finiteState Q I H hH M).scalar := by
    simpa only [Nat.add_sub_of_le hMN, finiteState] using hs.2.1
  have hse : (iteration (Q.map (Ideal.Quotient.mk (I ^ M))) (quotientBaseIdeal I M) (quotientBaseIdeal_isNilpotent I M)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H) (quotientBaseError_mem I H hH M) N).equiv =
      (finiteState Q I H hH M).equiv := by
    simpa only [Nat.add_sub_of_le hMN, finiteState] using hs.2.2
  refine ⟨hn.1.trans hsc, ?_, ?_⟩
  · intro g
    exact (hn.2.2 g).trans (congrArg (fun e => e (MvPowerSeries.map f g)) hse)
  · intro g
    have hi := iteration_symm_map (Q.map (Ideal.Quotient.mk (I ^ N))) f (quotientBaseIdeal I N) (quotientBaseIdeal I M)
      (quotientBaseIdeal_isNilpotent I N) (quotientBaseIdeal_isNilpotent I M)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) H)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ M)) H)
      (quotientBaseError_mem I H hH N) (quotientBaseError_mem I H hH M) he N g
    rw [hQ, hse] at hi
    exact hi

/-- The finite scalar at the original first quotient vanishes internally. -/
theorem finiteState_one_scalar (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) :
    (finiteState Q I H hH 1).scalar = 0 := by
  have hz : MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H = 0 := by
    ext d
    rw [coeff_map, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [pow_one] using hH d)
  have hs := iteration_stable (Q.map (Ideal.Quotient.mk (I ^ 1))) (quotientBaseIdeal I 1) (quotientBaseIdeal_isNilpotent I 1)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H) (quotientBaseError_mem I H hH 1) 0 1 hz
  exact hs.2.1

/-- The actual first finite map is the identity, not merely pointwise equal on variables. -/
theorem finiteState_one_equiv (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) :
    (finiteState Q I H hH 1).equiv = AlgEquiv.refl := by
  have hz : MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H = 0 := by
    ext d
    rw [coeff_map, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [pow_one] using hH d)
  have hs := iteration_stable (Q.map (Ideal.Quotient.mk (I ^ 1))) (quotientBaseIdeal I 1) (quotientBaseIdeal_isNilpotent I 1)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) H) (quotientBaseError_mem I H hH 1) 0 1 hz
  exact hs.2.2

end Hironaka.Algebra.NodeNonsplit
