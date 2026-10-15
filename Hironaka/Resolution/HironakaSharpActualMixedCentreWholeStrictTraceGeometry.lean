/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualDiscreteCentreMemberLocalBranch

/-! Actual WHOLE ambient strict-trace coherence/nonzero/principality and density
under ANY discrete centre, before chronological factor or tauD comparisons. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualMixedCentreWholeStrictTraceGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualDiscreteCentreMemberLocalBranch HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct
  HironakaOneDimensionalCanonicalSuperlevels PositiveDimensionalComponent
  RelativePrincipalizationSpan RestrictedIdealExtension NormalCrossings DivisorExponentAlong
  HironakaCoherentTransformExtension MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine actual finite pullback spans and actual strict membership give the
WHOLE ambient inclusion, without coherence of either vanishing ideal. -/
theorem actual_pullback_vanishing_le_strict_vanishing {H C : Set X} (hH : IsClosed H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).Le
      (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)) := by
  intro z g hg
  obtain ⟨hgh,r,s,a,hs,_ha,hEq⟩ := GermIdeal.mem_pullback_iff.mp hg
  have hEach (i : Fin r) : ∀ᶠ y in 𝓝 z,y ∈ BlowupStrictSubmanifold.geoStrictTransform π C H → s i y=0 := by
    obtain ⟨b,hb,he⟩ := hs i
    rw [he]
    filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hb.2] with y hy hyH
    exact hy (BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH hyH)
  refine ⟨hgh,?_⟩
  filter_upwards [eventually_all.mpr hEach,hEq] with y hy heq hyH
  rw [heq]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [hy i hyH,mul_zero]

/-- True relative finite-span vanishing and actual frequent nonzero witnesses
supply genuine carrier density, with no smoothness or coherence premise. -/
theorem actual_density_of_nonzero_normalized_vanishing {N H : Set X}
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) x) :
    N ⊆ closure (N \ H) := by
  intro x hx
  obtain ⟨g,hg,hfreq⟩ := hnz x hx
  obtain ⟨r,s,a,hs,_ha,hEq⟩ := hg.2
  have hZero : ∀ᶠ y in 𝓝 x,y ∈ N → y ∈ H → g y=0 := by
    filter_upwards [eventually_all.mpr (fun i : Fin r => (hs i).2),hEq] with y hy heq hyN hyH
    rw [heq hyN]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hy i hyH,mul_zero]
  apply mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨y,hy⟩ := ((hfreq.and_eventually hZero).and_eventually (hU.mem_nhds hxU)).exists
  exact ⟨y,hy.2,hy.1.1.1,fun hyH => hy.1.1.2 (hy.1.2 hy.1.1.1 hyH)⟩

/-- ONLY original actual SNC/density and ANY real discrete centre internally
produce WHOLE true next trace geometry, including real new density. -/
theorem actual_mixed_discrete_centre_whole_strict_trace_geometry (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
    let I' := restrictOn n N' (vanishingIdeal (n := n) H')
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n [H',π ⁻¹' C] ∧
      I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      N' ⊆ closure (N' \ H') ∧
      ∀ y ∈ N',∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,I'.mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N' (·=f) y g := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
  let I' := restrictOn n N' (vanishingIdeal (n := n) H')
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hNC : HasNormalCrossings n C [H] := by
    apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
    intro x hx
    obtain ⟨O,hO,hxO,hIso⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hrC x hx)
    refine ⟨{x},mem_singleton x,?_,hasNormalCrossings_singleton x hH⟩
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact ⟨fun hyC => hIso ⟨hyC,hy⟩,fun hyx => by rw [mem_singleton_iff.mp hyx]; exact hx⟩
  have hAmbient := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hH hNC
  have hH' : IsClosedSubmanifold n H' := MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  have hcI : I'.IsCoherent := isCoherent_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hH')
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  have hRaw : (M0.geoTransform C π).ideal=P := geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hRaw]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hcH hπ hCN hnzH
  have hLe := actual_pullback_vanishing_le_strict_vanishing hHc.1 hπ
  have hPI : P.Le I' := by
    intro y g hg
    exact ⟨hg.1,IsInSpanOnAt.mono (fun a ha => hLe y a ha) hg.2⟩
  have hnzI : ∀ y ∈ N',IsNonzeroAlongAt N' I' y := by
    intro y hy
    obtain ⟨g,hg,hfreq⟩ := hnzP y hy
    exact ⟨g,hPI y g hg,hfreq⟩
  refine ⟨hN',by simpa only [List.map_singleton,List.singleton_append] using hAmbient,
    hcI,hnzI,actual_density_of_nonzero_normalized_vanishing hnzI,?_⟩
  intro y _hy
  obtain ⟨f,hf,hgen⟩ := exists_originalMember_principal hn hAmbient (H := H') (by simp [H']) y
  exact ⟨f,hf,fun g => and_congr_right fun _ => restricted_span_iff_principal hf hgen g⟩

end
end Hironaka.HironakaSharpActualMixedCentreWholeStrictTraceGeometry
