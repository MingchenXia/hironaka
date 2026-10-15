/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStrictTraceContactDrop

/-! Genuine curve member isolation identifies actual exceptional exponent
with actual point order, then computes the true remaining first-step factor. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveExceptionalPointExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveStrictTraceContactDrop HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpActualCurveExceptionalResidualUnit HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NormalCrossings GermIdealOrder IdealWeightPowers
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual SNC/curve geometry supplies true isolation BEFORE literal nearby
cosupport predicates identify the actual greatest exponent with actual order. -/
theorem actual_curve_member_divExp_eq_ordinaryTraceOrder (hn : 0 < n)
    {N : Set X} (hN : IsClosedSubmanifold n N) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hcI : I.IsCoherent) (hnzI : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : X} (hr : RegularAtDim (n := n) N x 1) (i : Fin E.length) (hxi : x ∈ E.get i) :
    divExpAlong n N I (E.get i) x=ordinaryTraceOrder N I x := by
  have hx : x ∈ N := hr.2.1
  obtain ⟨U,hU,hxU,hSub⟩ := exists_actual_curve_member_isolating_open hn hE hT hr i hxi
  have hiff (q : ℕ) : IsDivNearAlong n N I (E.get i) q x ↔ x ∈ cosupport n N I q := by
    constructor
    · exact fun h => h.self_of_nhds hx hxi
    · intro hq
      filter_upwards [hU.mem_nhds hxU] with y hy hyN hyH
      have he : y=x := hSub ⟨⟨hyN,hyH⟩,hy⟩
      simpa only [he] using hq
  obtain ⟨d,hd⟩ := hN.2 x hx
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hd
  have hhol : ∀ y g,I.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcI hg
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx _).mp
    exact (hiff _).mp (isDivNearAlong_divExpAlong hhol x)
  · apply (isDivNearAlong_iff_le_divExpAlong hr hxi (hnzI x hx) hhol).mp
    exact (hiff _).mpr ((ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx _).mpr le_rfl)

/-- ONLY original first-step geometry computes the real remaining exceptional
exponent and BOTH full relative germ directions of the actual greatest factor. -/
theorem actual_first_curve_remaining_factor_exponent_and_germs (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    (hH : IsSNCDivisor n [H]) (hdense : N ⊆ closure (N \ H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N ∩ π ⁻¹' C) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let D := π ⁻¹' C
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let r := ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z)
    divExpAlong n N' I' D z+1=r ∧
      ∀ g,(monomialPartAlong n N' I' [D]).mem z g ↔ HolomorphicAt n g z ∧
        IsInSpanOnAt (n := n) N' ((idealPow (vanishingIdeal (n := n) D) (r-1)).mem z) z g := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let D := π ⁻¹' C
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  let a := ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z)
  obtain ⟨hN',hD,hT,hcI,hnzI,_hprI⟩ := actual_first_ambient_strict_trace_relative_geometry hn hN hH hdense hπ hCN hCH
  have hr' : RegularAtDim (n := n) N' z 1 :=
    BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hN.1 hrN hCN hz.1
  have hExp : divExpAlong n N' I' D z=ordinaryTraceOrder N' I' z :=
    actual_curve_member_divExp_eq_ordinaryTraceOrder hn hN' hD hT hcI hnzI hr' (0 : Fin [D].length) hz.2
  have hDrop := (actual_first_curve_ambient_strict_trace_order_drop hn hN hrN hrC hH hdense hπ hCN hCH hz).1
  have hComputed : divExpAlong n N' I' D z+1=a := by rw [hExp]; exact hDrop
  have hValue : divExpAlong n N' I' D z=a-1 := by omega
  refine ⟨hComputed,?_⟩
  intro g
  constructor
  · rintro ⟨hg,hM⟩
    refine ⟨hg,?_⟩
    have hp := hM (0 : Fin [D].length) hz.1 hz.2
    change IsInSpanOnAt (n := n) N' ((idealPow (vanishingIdeal (n := n) D) (divExpAlong n N' I' D z)).mem z) z g at hp
    rw [hValue] at hp
    exact hp
  · rintro ⟨hg,hp⟩
    refine ⟨hg,?_⟩
    intro i _hN _hD
    have hi : i=(0 : Fin [D].length) := by
      apply Fin.ext
      change i.val=0
      have hh := i.isLt
      simp only [List.length_singleton] at hh
      omega
    subst i
    change IsInSpanOnAt (n := n) N' ((idealPow (vanishingIdeal (n := n) D) (divExpAlong n N' I' D z)).mem z) z g
    rw [hValue]
    exact hp

end
end Hironaka.HironakaSharpActualCurveExceptionalPointExponent
