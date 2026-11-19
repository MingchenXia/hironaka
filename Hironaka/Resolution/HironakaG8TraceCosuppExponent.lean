import Hironaka.Resolution.HironakaG8CommonGenericOrder
import Hironaka.Resolution.HironakaActualProjectedNormalizedOrderDetection
import Hironaka.Resolution.HironakaG8LocalHistory
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8TraceCosuppExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec GermIdealOrder
  DivisorExponentAlong HironakaSharpOriginalProductTraceOrder HironakaG8CommonGenericOrder
  HironakaG8LocalHistory HironakaG8ProjEquiv HironakaActualProjectedNormalizedOrderDetection

/-- Local projected equivalence detects normalized divisor exponents when
the selected boundary trace belongs to the common cosupport as a germ. -/
theorem normalized_exponent_of_trace_cosupp {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k l : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (i : Fin A.E.length) (j : Fin B.E.length)
    (hH : A.E.get i = B.E.get j) {x : X} (hxN : x ∈ A.N) (hxH : x ∈ A.E.get i)
    (hTrace : ∀ᶠ y in 𝓝 x, y ∈ A.N → y ∈ A.E.get i → y ∈ A.cosupp) :
    B.d * divExpAlong n A.N A.ideal (A.E.get i) x =
      A.d * divExpAlong n B.N B.ideal (B.E.get j) x := by
  have hf := frequently_common_generic_order hn A B hA hB hN i j hH hxN hxH
  obtain ⟨y,hy,hyTrace⟩ := (hf.and_eventually hTrace).exists
  have hyA : y ∈ A.cosupp := hyTrace hy.1 hy.2.1
  have hyB : y ∈ B.cosupp := hL.cosupp_eq_base ▸ hyA
  have ho := (normalized_ordinary_order_of_projected_wEquiv A B hA hB y hyA hyB
    hN.symm hL.E_eq hL.projEquiv.projectionTest_wEquiv).2.2
  simpa only [hy.2.2.1,hy.2.2.2] using ho

/-- In particular the normalized exponents agree whenever the selected
source exponent is at least the source mark. -/
theorem normalized_exponent_of_mark_le {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k l : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (i : Fin A.E.length) (j : Fin B.E.length)
    (hH : A.E.get i = B.E.get j) {x : X} (hxN : x ∈ A.N) (hxH : x ∈ A.E.get i)
    (hmark : A.d ≤ divExpAlong n A.N A.ideal (A.E.get i) x) :
    B.d * divExpAlong n A.N A.ideal (A.E.get i) x =
      A.d * divExpAlong n B.N B.ideal (B.E.get j) x := by
  apply normalized_exponent_of_trace_cosupp hn A B hA hB hN hL i j hH hxN hxH
  have hhol : ∀ z f, A.ideal.mem z f → HolomorphicAt n f z :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hf
  have hdiv := isDivNearAlong_divExpAlong (N := A.N) (H := A.E.get i) hhol x
  filter_upwards [hdiv] with y hy hyN hyH
  exact cosupport_anti hmark (hy hyN hyH)

end
end Hironaka.HironakaG8TraceCosuppExponent
