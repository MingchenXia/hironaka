/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMixedDiscreteTraceResidual

/-! Whole OLD-accumulated boundary residual comparison from actual mixed
trace and raw factorizations; no singleton substitution for the full list. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualAccumulatedTraceResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualMixedDiscreteTraceResidual HironakaSharpActualRawMemberOpenStrict
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry HironakaSharpActualRelativeMonomialProduct
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaCoherentTransformExtension RelativePrincipalizationSpan RestrictedIdealExtension
  RestrictedIdealQuotient MonomialPartAlong DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal RestrictLeCalculus NonmonomialTransformAlong
  InvertibleIdealQuotient HironakaOneDimensionalCanonicalSuperlevels PositiveDimensionalComponent
  MarkedIdealOperationsAlong IdealWeightPowers RestrictedIdealWeight
  HironakaSharpActualControlledRelativeSaturation
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Every genuine smaller-family constraint is present in the larger family's
actual monomial part. This is not a statement about indexed trace counts. -/
theorem actual_isMonomialAlong_of_family_subset {N : Set X} {E F : List (Set X)}
    (hEF : ∀ H ∈ E,H ∈ F) {I : GermIdeal n X} (hmono : IsMonomialAlong n N I E) :
    IsMonomialAlong n N I F := by
  intro x hx g hg
  apply hmono x hx g
  refine ⟨hg.1,?_⟩
  intro i hiN hiE
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (hEF (E.get i) (List.get_mem E i))
  have hxF : x ∈ F.get j := by rw [hj]; exact hiE
  simpa only [hj] using hg.2 j hiN hxF

/-- Actual whole normalized monomial products have the SAME residual, from
genuine parts and true factor uniqueness, not a supplied quotient identity. -/
theorem actual_normalized_monomial_product_nonmonomial_eq (hn : 0 < n)
    {N : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {A B : GermIdeal n X} (hcA : A.IsCoherent) (hcB : B.IsCoherent)
    (hnzA : ∀ x ∈ N,IsNonzeroAlongAt N A x) (hnzB : ∀ x ∈ N,IsNonzeroAlongAt N B x)
    (hmA : IsMonomialAlong n N A E) :
    nonmonomialPartAlong n N (restrictOn n N (A.mul B)) E=nonmonomialPartAlong n N B E := by
  let R := nonmonomialPartAlong n N B E
  let M := monomialPartAlong n N B E
  let H := A.mul M
  let I := restrictOn n N (A.mul B)
  obtain ⟨hcR,hcM,hnzM,hmM,hndR,_hnzR,hEqB⟩ := parts_hypotheses hn
    (⟨N,E,B,0⟩ : MarkedIdeal n X) ⟨hN,hcB,hE,hT⟩ hnzB
  obtain ⟨hcH,hnzH,hmH⟩ := actual_relative_monomial_product_geometry hn hN hE hT hcA hcM hnzA hnzM hmA hmM
  have hAssoc : A.mul (R.mul M)=R.mul H := by
    rw [←GermIdealTotalTransform.mul_assoc hcA hcR hcM,mul_comm' A R,
      GermIdealTotalTransform.mul_assoc hcR hcA hcM]
  have hForward := restrictLe_mul
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_mul hcR hcM) hg)
    (restrictLe_refl hcA) hEqB.le
  have hBackward := restrictLe_mul
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcB hg)
    (restrictLe_refl hcA) hEqB.ge
  change RestrictLe N (A.mul B) (A.mul (R.mul M)) at hForward
  change RestrictLe N (A.mul (R.mul M)) (A.mul B) at hBackward
  rw [hAssoc] at hForward hBackward
  have hf : RestrictLe N I (R.mul H) := RestrictLeCalculus.RestrictLe.trans restrictLe_restrictOn hForward
  have hb : RestrictLe N (R.mul H) I := RestrictLeCalculus.RestrictLe.trans hBackward
    (restrictLe_self_restrictOn (isCoherent_mul hcA hcB))
  have hM := monomialPartAlong_eq_of_factor hn hN hE hT hcR hcH hndR hf hb
  have hlo : R.Le (nonmonomialPartAlong n N I E) := le_nonmonomialPartAlong_of_factor hN.1
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcR hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcH hg) hmH hM hb
  have hup : RestrictLe N (nonmonomialPartAlong n N I E) R :=
    restrictLe_nonmonomialPartAlong_of_factor hn hN hE hT hcR hcH hnzH hmH hM hf
  ext x g
  constructor
  · intro hg
    by_cases hx : x ∈ N
    · exact (restrictOn_colonAlong_mem_iff N B M
        (fun a ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcM ha) g).mp
        ⟨hg.1,hup x hx g hg⟩
    · refine ⟨hg.1,fun a ha => ?_⟩
      exact restrictOn_eq_top_of_disjoint (W := N) (𝔞 := B) hN.1.isOpen_compl hx (by simp) (ha.1.mul hg.1)
  · exact fun hg => hlo x g hg

/-- Genuine zero-dimensional regularity supplies actual NC with every original
SNC member at once; no desired admissibility geometry is input. -/
theorem actual_discrete_centre_hasNormalCrossings {C : Set X}
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0) {E : List (Set X)} (hE : IsSNCDivisor n E) :
    HasNormalCrossings n C E := by
  apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
  intro x hx
  obtain ⟨O,hO,hxO,hIso⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hrC x hx)
  refine ⟨{x},mem_singleton x,?_,hasNormalCrossings_singleton x hE⟩
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact ⟨fun hyC => hIso ⟨hyC,hy⟩,fun hyx => by rw [mem_singleton_iff.mp hyx]; exact hx⟩

/-- ONLY original mixed discrete-centre data give true ALL-old-E geometry
and WHOLE trace versus actual raw TOTAL residual equality for the SAME Enew. -/
theorem actual_mixed_discrete_accumulated_trace_nonmonomial_eq_total (hn : 0 < n)
    {N H C : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
    IsSNCDivisor n E' ∧ IsTransverse n N' E' ∧ nonmonomialPartAlong n N' I' E'=nonmonomialPartAlong n N' P E' := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  let J := HironakaSharpOriginalFirstMemberRelativeStrict.firstRelativeStrictMemberIdeal N H C π
  let Dt := monomialPartAlong n N' I' [π ⁻¹' C]
  let Dr := monomialPartAlong n N' P [π ⁻¹' C]
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hNC := actual_discrete_centre_hasNormalCrossings hrC hE
  obtain ⟨hENew,hTNew⟩ := actual_accumulated_exceptional_geometry hN hcH hE hT hπ hCN hNC
  change IsTransverse n N' E' at hTNew
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hcP : P.IsCoherent := isCoherent_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcH)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  have hRaw := geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  change (M0.geoTransform C π).ideal=P at hRaw
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hRaw]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hcH hπ hCN hnzH
  obtain ⟨hESingle,hTSingle⟩ := actual_accumulated_exceptional_geometry hN hcH isSNCDivisor_nil
    (isTransverse_nil_of_isClosedSubmanifold hN) hπ hCN (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
  change IsSNCDivisor n [π ⁻¹' C] at hESingle
  change IsTransverse n N' [π ⁻¹' C] at hTSingle
  obtain ⟨hcR,hcDr,hnzDr,hmDr,_hNo,hnzR,hFactor⟩ := parts_hypotheses hn
    (⟨N',[π ⁻¹' C],P,0⟩ : MarkedIdeal n Y) ⟨hN',hcP,hESingle,hTSingle⟩ hnzP
  have hRJ : nonmonomialPartAlong n N' P [π ⁻¹' C]=J :=
    actual_any_member_raw_nonmonomial_eq_relative_strict hn hN hH hdense hπ hCN
  have hcJ : J.IsCoherent := hRJ ▸ hcR
  have hnzJ : ∀ y ∈ N',IsNonzeroAlongAt N' J y := hRJ ▸ hnzR
  have hFRaw := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN'.1 hFactor.le hFactor.ge
  change restrictOn n N' P=restrictOn n N' ((nonmonomialPartAlong n N' P [π ⁻¹' C]).mul Dr) at hFRaw
  rw [hRJ,mul_comm' J Dr] at hFRaw
  have hNorm : restrictOn n N' P=P := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  have hPRaw : P=restrictOn n N' (Dr.mul J) := hNorm.symm.trans hFRaw
  obtain ⟨hcDt,hnzDt,hmDt,hPTrace⟩ := actual_mixed_discrete_trace_greatest_factor_dictionary hn hN hH hdense hrC hπ hCN
  have hSub : ∀ A ∈ [π ⁻¹' C],A ∈ E' := by
    intro A hA
    exact List.mem_append_right _ hA
  have hmDrAll : IsMonomialAlong n N' Dr E' := actual_isMonomialAlong_of_family_subset hSub hmDr
  have hmDtAll : IsMonomialAlong n N' Dt E' := actual_isMonomialAlong_of_family_subset hSub hmDt
  have hRawEq := actual_normalized_monomial_product_nonmonomial_eq hn hN' hENew hTNew hcDr hcJ hnzDr hnzJ hmDrAll
  have hTraceEq := actual_normalized_monomial_product_nonmonomial_eq hn hN' hENew hTNew hcDt hcJ hnzDt hnzJ hmDtAll
  change nonmonomialPartAlong n N' (restrictOn n N' (Dr.mul J)) E'=nonmonomialPartAlong n N' J E' at hRawEq
  change nonmonomialPartAlong n N' (restrictOn n N' (Dt.mul J)) E'=nonmonomialPartAlong n N' J E' at hTraceEq
  rw [←hPRaw] at hRawEq
  change I'=restrictOn n N' (Dt.mul J) at hPTrace
  rw [←hPTrace] at hTraceEq
  exact ⟨hENew,hTNew,hTraceEq.trans hRawEq.symm⟩

end
end Hironaka.HironakaSharpActualAccumulatedTraceResidual
