import Hironaka.Resolution.HironakaG1NormalizedGammaCuts

/-! Full monomial gamma cuts across two different actual head manifolds. -/
set_option autoImplicit false
open Set Finset TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1CrossHeadGammaCuts
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  MonomialCase MonomialCaseAlong NonmonomialOrderLocal HironakaG1NormalizedGammaCuts

private theorem feasible_of_zero {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) {x : X} (hx : x ∈ M.cosupp) (hzero : nmOrd M x = 0) :
    M.d ≤ ∑ i ∈ memberIdx M.E x, expDataAlong n M.N M.ideal M.E x i := by
  obtain ⟨_,_,hord,_⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order
    hn M hM.isWellFormed hM.isNonzeroAlongAt x (M.cosupp_subset_N hx)
  have hmark := HironakaG8MixedOrderInvariance.mark_le_ordinaryTraceOrder M hM hx
  rw [hord,hzero,Nat.add_zero] at hmark
  exact hmark

/-- Cross-scaled exponents compare the complete original gamma values at two
points even when their actual lower records live on different stage types. -/
theorem gamma_cut_iff_across_heads {n kAz kBz kAw : ℕ} (hn : 0 < n)
    {Xz Xw : CMfd.{0} n} (Az Bz : MarkedIdeal n Xz) (Aw Bw : MarkedIdeal n Xw)
    (hAz : IsInvDomain kAz Az) (hBz : IsInvDomain kBz Bz)
    (hAw : IsInvDomain kAw Aw)
    (hEz : Az.E = Bz.E) (hEw : Aw.E = Bw.E)
    (hAd : Az.d = Aw.d) (hBd : Bz.d = Bw.d)
    (z : Xz) (w : Xw)
    (hz : z ∈ Az.cosupp) (hw : w ∈ Aw.cosupp) (hz0 : nmOrd Az z = 0) (hw0 : nmOrd Aw w = 0)
    (hExpZ : ∀ i, Bz.d * expDataAlong n Az.N Az.ideal Az.E z i =
      Az.d * expDataAlong n Bz.N Bz.ideal Bz.E z i)
    (hExpW : ∀ i, Bw.d * expDataAlong n Aw.N Aw.ideal Aw.E w i =
      Aw.d * expDataAlong n Bw.N Bw.ideal Bw.E w i) :
    gammaAlong n Az.N Az.ideal Az.E Az.d z < gammaAlong n Aw.N Aw.ideal Aw.E Aw.d w ↔
      gammaAlong n Bz.N Bz.ideal Bz.E Bz.d z < gammaAlong n Bw.N Bw.ideal Bw.E Bw.d w := by
  have hIdxZ : memberIdx Az.E z = memberIdx Bz.E z := by rw [hEz]
  have hIdxW : memberIdx Aw.E w = memberIdx Bw.E w := by rw [hEw]
  have hfeasZ := feasible_of_zero hn Az hAz hz hz0
  have hfeasW := feasible_of_zero hn Aw hAw hw hw0
  unfold gammaAlong
  rw [←hIdxZ,←hIdxW,←hAd,←hBd]
  apply normalized_inv_lt_iff n _ _ _ _ _ _ _ _ hAz.one_le_d hBz.one_le_d
  · intro i _; exact hExpZ i
  · intro i _; simpa only [←hAd,←hBd] using hExpW i
  · exact hfeasZ
  · simpa only [←hAd] using hfeasW
end Hironaka.HironakaG1CrossHeadGammaCuts
