import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Invariant.DivisorExponentAlong

/-! The actual generic order along a trace equals its divisor exponent.
Blueprint: `hironaka-g8-boundary-generic-order.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8BoundaryGenericOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  DivisorExponentAlong RelativePrincipalizationSpan GermIdealOrder
  HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X : CMfd.{0} n}

/-- Arbitrarily close on the trace, ordinary order is exactly the actual
divisor exponent. No global generic-point choice is assumed. -/
theorem frequently_order_eq_divisor_exponent {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (H : Set X) {x : X} (hxN : x ∈ M.N) (hxH : x ∈ H) :
    ∃ᶠ y in 𝓝 x, y ∈ M.N ∧ y ∈ H ∧
      ordinaryTraceOrder M.N M.ideal y = divExpAlong n M.N M.ideal H x := by
  let β := divExpAlong n M.N M.ideal H x
  have hhol : ∀ z f, M.ideal.mem z f → HolomorphicAt n f z :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hf
  obtain ⟨r,hr⟩ := exists_isLocalRetraction ((hM.isWellFormed.isClosedSubmanifold_N.2 x hxN).choose_spec)
  have hgood : IsDivNearAlong n M.N M.ideal H β x := isDivNearAlong_divExpAlong hhol x
  have hbad : ¬ IsDivNearAlong n M.N M.ideal H (β+1) x :=
    not_isDivNearAlong_divExpAlong_succ hr hxH (hM.isNonzeroAlongAt x hxN) hhol
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ M.N ∧ y ∈ H ∧ y ∉ cosupport n M.N M.ideal (β+1) := by
    apply Filter.frequently_iff.mpr
    intro U hU
    by_contra hnone
    apply hbad
    filter_upwards [hU] with y hy hyN hyH
    by_contra hybad
    exact hnone ⟨y,hy,hyN,hyH,hybad⟩
  refine (hfreq.and_eventually hgood).mono ?_
  intro y ⟨⟨hyN,hyH,hybad⟩,hyGood⟩
  refine ⟨hyN,hyH,?_⟩
  have hlo := (ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.isNonzeroAlongAt hyN β).mp (hyGood hyN hyH)
  have hhi : ¬ β+1 ≤ ordinaryTraceOrder M.N M.ideal y := fun h => hybad
    ((ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.isNonzeroAlongAt hyN (β+1)).mpr h)
  change ordinaryTraceOrder M.N M.ideal y = β
  omega
end
end Hironaka.HironakaG8BoundaryGenericOrder
