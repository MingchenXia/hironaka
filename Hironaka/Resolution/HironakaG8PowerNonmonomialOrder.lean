import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Resolution.HironakaActualPowerBoundaryExponents

/-! Whole-power scaling of the native nonmonomial order, including boundary points. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerNonmonomialOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  NonmonomialOrderLocal MonomialCaseAlong MonomialInvariant MonomialCase BoundaryCount
  HironakaActualCoefficientNonmonomialHistoryOrder HironakaActualPowerBoundaryExponents
  HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X : CMfd.{0} n}

/-- Every actual native boundary exponent of a positive whole power scales. -/
theorem expDataAlong_powerMarked (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {e : ℕ} (he : 1 ≤ e) (y : X) (i : ℕ) :
    expDataAlong n (powerMarked M e).N (powerMarked M e).ideal (powerMarked M e).E y i =
      e * expDataAlong n M.N M.ideal M.E y i := by
  unfold powerMarked expDataAlong
  split
  · rename_i hi
    rw [divExpAlong_idealPow hM.isClosedSubmanifold_N hM.isCoherent he y]
  · simp

/-- The raw nonmonomial order of a positive whole power scales at every
point of the actual carrier, including points on the exceptional boundary. -/
theorem nmOrd_powerMarked {k : ℕ} (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e) {y : X} (hy : y ∈ M.N) :
    nmOrd (powerMarked M e) y = e * nmOrd M y := by
  have hP := powerMarked_isInvDomain M hM he
  have hO := (whole_factor_order hn M hM.isWellFormed hM.isNonzeroAlongAt y hy).2.2.1
  have hOP := (whole_factor_order hn (powerMarked M e) hP.isWellFormed hP.isNonzeroAlongAt y hy).2.2.1
  have hPow := ordinaryTraceOrder_idealPow hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.isNonzeroAlongAt he hy
  have hSum : (∑ i ∈ memberIdx M.E y, expDataAlong n M.N (powerMarked M e).ideal M.E y i) =
      e * ∑ i ∈ memberIdx M.E y, expDataAlong n M.N M.ideal M.E y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact expDataAlong_powerMarked M hM.isWellFormed he y i
  change ordinaryTraceOrder M.N (powerMarked M e).ideal y =
    (∑ i ∈ memberIdx M.E y, expDataAlong n M.N (powerMarked M e).ideal M.E y i) +
      nmOrd (powerMarked M e) y at hOP
  change ordinaryTraceOrder M.N (powerMarked M e).ideal y = e * ordinaryTraceOrder M.N M.ideal y at hPow
  rw [hSum] at hOP
  rw [hO, Nat.mul_add] at hPow
  omega

end
end Hironaka.HironakaG8PowerNonmonomialOrder
