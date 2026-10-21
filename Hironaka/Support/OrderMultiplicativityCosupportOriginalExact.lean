/- Complete original prerequisite; statement and mathematical proof unchanged. -/
import Hironaka.Invariant.OrderMultiplicativity

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.OrderMultiplicativity

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.OrderTaylor
  Hironaka.HolomorphicTaylorTail Hironaka.IdealOrderArithmetic
  Hironaka.RestrictedIdealExtension Hironaka.HolomorphicAnalytic

noncomputable section

section Iterated

variable {n : ℕ}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {𝔞 𝔟 : GermIdeal n M}

/-- **`cosupp(𝔞^ν, μν) = cosupp(𝔞, μ)`** for `ν ≥ 1` (`N = M`, `𝔞` an ideal of holomorphic germs). -/
theorem cosupport_idealPow_mul_eq (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {ν : ℕ} (hν : 1 ≤ ν)
    (μ : ℕ) : cosupport n univ (idealPow 𝔞 ν) (μ * ν) = cosupport n univ 𝔞 μ := by
  refine Subset.antisymm ?_ (cosupport_subset_cosupport_idealPow μ ν)
  rintro x ⟨-, hx⟩
  refine ⟨mem_univ x, fun g hg => ⟨g, ?_, Eventually.of_forall fun _ _ => rfl⟩⟩
  have hpow := mem_idealPow_of_vanishesToOrderOn_univ (hx _ (pow_mem_idealPow hg (h𝔞 x g hg) ν))
  rw [Nat.mul_comm] at hpow
  exact mem_idealPow_of_pow_mem (h𝔞 x g hg) hν hpow

end Iterated

end

end Hironaka.OrderMultiplicativity

