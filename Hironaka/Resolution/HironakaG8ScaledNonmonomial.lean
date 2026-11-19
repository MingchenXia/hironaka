import Hironaka.Resolution.HironakaG8PowerNonmonomialOrder

/-! Recover normalized nonmonomial order from whole order and boundary powers.
Blueprint: `hironaka-g8-scaled-nonmonomial.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ScaledNonmonomial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  NonmonomialOrderLocal MonomialCaseAlong MonomialCase BoundaryCount DivisorExponentAlong
  HironakaActualCoefficientNonmonomialHistoryOrder HironakaSharpOriginalProductTraceOrder
variable {n : ℕ} {X : CMfd.{0} n}

/-- At a common-carrier point, cross-scaled whole order and every incident
boundary exponent imply cross-scaled nonmonomial order. -/
theorem scaled_nmOrd_of_scaled_data {k l : ℕ} (hn : 0 < n)
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N = P.N) (hE : Q.E = P.E) {y : X} (hy : y ∈ P.N)
    (hOrd : Q.d * ordinaryTraceOrder P.N P.ideal y = P.d * ordinaryTraceOrder Q.N Q.ideal y)
    (hExp : ∀ H ∈ P.E, y ∈ H →
      Q.d * divExpAlong n P.N P.ideal H y = P.d * divExpAlong n Q.N Q.ideal H y) :
    Q.d * nmOrd P y = P.d * nmOrd Q y := by
  have hQy : y ∈ Q.N := hN ▸ hy
  have hWP := (whole_factor_order hn P hP.isWellFormed hP.isNonzeroAlongAt y hy).2.2.1
  have hWQ := (whole_factor_order hn Q hQ.isWellFormed hQ.isNonzeroAlongAt y hQy).2.2.1
  have hSum : Q.d * (∑ i ∈ memberIdx P.E y, expDataAlong n P.N P.ideal P.E y i) =
      P.d * (∑ i ∈ memberIdx Q.E y, expDataAlong n Q.N Q.ideal Q.E y i) := by
    rw [hE,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := (mem_memberIdx P.E).mp hi
    simp only [expDataAlong,dif_pos hi'.1]
    exact hExp (P.E.get ⟨i,hi'.1⟩) (List.get_mem _ _) hi'.2
  rw [hWP,hWQ,Nat.mul_add,Nat.mul_add] at hOrd
  omega
end
end Hironaka.HironakaG8ScaledNonmonomial
