import Hironaka.Resolution.HironakaG8BoundaryGenericOrder
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CommonGenericOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec GermIdealOrder
  DivisorExponentAlong HironakaSharpOriginalProductTraceOrder HironakaG8BoundaryGenericOrder

/-- Both coherent records attain their own divisor-generic order at the same
nearby points of the common smooth boundary trace. -/
theorem frequently_common_generic_order {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k l : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : A.N = B.N) (i : Fin A.E.length) (j : Fin B.E.length)
    (hH : A.E.get i = B.E.get j) {x : X} (hxN : x ∈ A.N) (hxH : x ∈ A.E.get i) :
    ∃ᶠ y in 𝓝 x, y ∈ A.N ∧ y ∈ A.E.get i ∧
      ordinaryTraceOrder A.N A.ideal y = divExpAlong n A.N A.ideal (A.E.get i) x ∧
      ordinaryTraceOrder B.N B.ideal y = divExpAlong n B.N B.ideal (B.E.get j) x := by
  let a := divExpAlong n A.N A.ideal (A.E.get i) x
  let b := divExpAlong n B.N B.ideal (B.E.get j) x
  have hxBN : x ∈ B.N := hN ▸ hxN
  have hxBH : x ∈ B.E.get j := hH ▸ hxH
  have hAfreq := frequently_order_eq_divisor_exponent A hA (A.E.get i) hxN hxH
  have hBexp := eventually_divExpAlong_get_eq hn hB.isWellFormed.isClosedSubmanifold_N
    hB.isWellFormed.isSNCDivisor hB.isWellFormed.isTransverse hB.isWellFormed.isCoherent
    hB.isNonzeroAlongAt j hxBN hxBH
  have hhol : ∀ z f, A.ideal.mem z f → HolomorphicAt n f z :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hf
  have hAdiv := isDivNearAlong_divExpAlong (N := A.N) (H := A.E.get i) hhol x
  apply Filter.frequently_iff.mpr
  intro U hU
  have hV : {z | z ∈ U ∧ (z ∈ B.N → z ∈ B.E.get j →
      divExpAlong n B.N B.ideal (B.E.get j) z = b) ∧
      (z ∈ A.N → z ∈ A.E.get i → z ∈ cosupport n A.N A.ideal a)} ∈ 𝓝 x := by
    filter_upwards [hU,hBexp,hAdiv] with z hz hb ha
    exact ⟨hz,hb,ha⟩
  obtain ⟨V,hVU,hVo,hxV⟩ := mem_nhds_iff.mp hV
  obtain ⟨y,hyA,hyV⟩ := (hAfreq.and_eventually (hVo.mem_nhds hxV)).exists
  have hyBN : y ∈ B.N := hN ▸ hyA.1
  have hyBH : y ∈ B.E.get j := hH ▸ hyA.2.1
  have hyAupper : y ∉ cosupport n A.N A.ideal (a+1) := by
    intro hc
    have ho := (ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N
      hA.isWellFormed.isCoherent hA.isNonzeroAlongAt hyA.1 (a+1)).mp hc
    have hya : ordinaryTraceOrder A.N A.ideal y = a := hyA.2.2
    omega
  let V' := V ∩ (cosupport n A.N A.ideal (a+1))ᶜ
  have hV'o : IsOpen V' := hVo.inter
    (GiraudAlong.isClosed_cosupport_along hA.isWellFormed.isCoherent hA.isWellFormed.isClosedSubmanifold_N _).isOpen_compl
  have hyV' : y ∈ V' := ⟨hyV,hyAupper⟩
  have hBfreq := frequently_order_eq_divisor_exponent B hB (B.E.get j) hyBN hyBH
  obtain ⟨z,hzB,hzV'⟩ := (hBfreq.and_eventually (hV'o.mem_nhds hyV')).exists
  have hzV := hzV'.1
  have hzN : z ∈ A.N := hN.symm ▸ hzB.1
  have hzH : z ∈ A.E.get i := hH.symm ▸ hzB.2.1
  have hzData := hVU hzV
  have hzALow := (ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent hA.isNonzeroAlongAt hzN a).mp (hzData.2.2 hzN hzH)
  have hzAHigh : ¬ a+1 ≤ ordinaryTraceOrder A.N A.ideal z := fun h => hzV'.2
    ((ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N
      hA.isWellFormed.isCoherent hA.isNonzeroAlongAt hzN (a+1)).mpr h)
  have hAeq : ordinaryTraceOrder A.N A.ideal z = a := by omega
  have hBeq : ordinaryTraceOrder B.N B.ideal z = b := by
    rw [hzB.2.2, (hVU hyV).2.1 hyBN hyBH]
  exact ⟨z, hzData.1, hzN, hzH, hAeq, hBeq⟩

end
end Hironaka.HironakaG8CommonGenericOrder
