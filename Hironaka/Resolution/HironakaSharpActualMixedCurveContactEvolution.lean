/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveExceptionalDifference

/-! True mixed-centre ambient trace contact and NEW-exceptional exponent
recurrence. No global centre-in-every-member premise or tau_D decrease claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualMixedCurveContactEvolution
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualChronologicalAmbientTrace
  HironakaSharpActualFiniteChronologicalHistory HironakaCoherentTransformExtension
  HironakaSharpActualCurveExceptionalPointExponent HironakaSharpActualCurveStrictTraceContactDrop
  HironakaSharpActualDiscreteCentreMemberLocalBranch HironakaSharpActualStrictTraceOpenNonmonomial
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry HironakaSharpActualFirstGoodLowerDimension
  HironakaSharpActualOriginalControlledHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  RelativePrincipalizationSpan RestrictedIdealExtension NormalCrossings NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen BlowupRestrictOpen
  GermIdealOrder DivisorExponentAlong MonomialPartAlong HomogenizedGlueingTower IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual ordinary marked input and genuine open pullback, not an order model. -/
theorem actual_ordinary_trace_order_pullback_open (hn : 0 < n)
    {N : Set X} (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hcI : I.IsCoherent)
    (hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x) (U : Opens X) (z : U) :
    ordinaryTraceOrder (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) z=ordinaryTraceOrder N I z.val := by
  have h := NonmonomialOrderLocal.nmOrd_pullback_val hn (ordinaryTraceMarked_isWellFormed hN hcI) hnzI U z
  exact h

private theorem actual_ordinary_order_zero_of_unit {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hcI : I.IsCoherent) (hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {x : X} (hx : x ∈ N) (h1 : I.mem x (1 : X → ℂ)) : ordinaryTraceOrder N I x=0 := by
  have hnle : ¬1 ≤ ordinaryTraceOrder N I x := by
    intro h
    have hCos := (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx 1).mpr h
    exact one_ne_zero ((vanishesToOrderOn_one_iff hx (holomorphicAt_const 1)).mp (hCos.2 1 h1))
  omega

/-- ANY actual discrete centre: the true ambient strict contact drops by
the actual incidence indicator, including points ABOVE the centre. -/
theorem actual_mixed_curve_ambient_strict_trace_order_evolution (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hH : IsSNCDivisor n [H]) (hdense : N ⊆ closure (N \ H))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∈ C) :
    ordinaryTraceOrder (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))) z+
      (if π z ∈ H then 1 else 0)=ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
  let I' := restrictOn n N' (vanishingIdeal (n := n) H')
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  obtain ⟨hN',hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_mixed_discrete_centre_whole_strict_trace_geometry hn hN hH hdense hrC hπ hCN
  have hH' : IsClosedSubmanifold n H' := MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  have hxN : π z ∈ N := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  by_cases hxH : π z ∈ H
  · obtain ⟨U,hxU,_hCU,hCH,_hAvoid⟩ := exists_actual_discrete_centre_member_open_branch hrC hHc.1 hzC
    let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V → U := fun y => ⟨π y,y.property⟩
    let NU : Set U := (Subtype.val : U → X) ⁻¹' N
    let HU : Set U := (Subtype.val : U → X) ⁻¹' H
    let CU : Set U := (Subtype.val : U → X) ⁻¹' C
    let zU : V := ⟨z,hxU⟩
    have hρ : IsBlowupAlong n CU ρ := isBlowupAlong_restrict hπ U V.isOpen
    have hNU : IsClosedSubmanifold n NU := isClosedSubmanifold_preimage_val hN U
    have hrNU : ∀ x ∈ NU,RegularAtDim (n := n) NU x 1 :=
      fun x hx => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hrN x.val hx)
    have hHU : IsSNCDivisor n [HU] := by
      simpa only [List.map_singleton] using NormalCrossingsInvariance.isSNCDivisor_map_preimage
        (NormalCrossingsInvariance.pullsBackCoordinates_val U) continuous_subtype_val hH
    have hDenseU : NU ⊆ closure (NU \ HU) := by
      intro x hx
      have hcl : x ∈ (Subtype.val : U → X) ⁻¹' closure (N \ H) := hdense hx
      have hEq := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val (N \ H)
      exact (Set.ext_iff.mp hEq x).mp hcl
    have hrCU : ∀ x ∈ CU,RegularAtDim (n := n) CU x 0 :=
      fun x hx => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hrC x.val hx)
    have hCNU : CU ⊆ NU := fun _ hx => hCN hx
    have hCHU : CU ⊆ HU := hCH hxH
    have hNEq := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen N
    have hHEq := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen H
    have hzU : zU ∈ BlowupStrictSubmanifold.geoStrictTransform ρ CU NU ∩ ρ ⁻¹' CU := by
      rw [hNEq]
      exact ⟨hz,hzC⟩
    have hDrop := (actual_first_curve_ambient_strict_trace_order_drop
      (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) hn hNU hrNU hrCU hHU hDenseU hρ hCNU hCHU hzU).1
    have hLocalIdeal : restrictOn n (BlowupStrictSubmanifold.geoStrictTransform ρ CU NU)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform ρ CU HU))=
        GermIdeal.pullback (m := n) (Subtype.val : V → Y) I' := by
      rw [hNEq,hHEq]
      exact actual_normalized_trace_whole_open_pullback hN' hH' V
    rw [hLocalIdeal,hNEq,actual_ordinary_trace_order_pullback_open hn hN' hcI hnzI V zU] at hDrop
    have hOld : ordinaryTraceOrder (X := CMfd.of (n := n) U) NU (vanishingIdeal (n := n) HU) (ρ zU)=
        ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) := by
      rw [←SmoothCentreHomogeneity.pullback_val_vanishingIdeal U H]
      exact actual_ordinary_trace_order_pullback_open hn hN hcH hnzH U (ρ zU)
    rw [hOld] at hDrop
    simpa only [if_pos hxH] using hDrop
  · have hzH : z ∉ H' := fun h => hxH
      (BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHc.1 h)
    have hI1 : I'.mem z (1 : Y → ℂ) := (actual_normalized_vanishing_unit_iff hH'.1 hz).mpr hzH
    have hH1 : (vanishingIdeal (n := n) H).mem (π z) (1 : X → ℂ) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hHc.1.isOpen_compl.mem_nhds hxH] with y hy hyH
      exact (hy hyH).elim
    have hNew := actual_ordinary_order_zero_of_unit hN' hcI hnzI hz hI1
    have hOld := actual_ordinary_order_zero_of_unit hN hcH hnzH hxN hH1
    simp only [hNew,hOld,if_neg hxH,zero_add]

/-- GENUINE NEW-exceptional greatest exponent from actual curve isolation,
without a global centre-in-member premise. -/
theorem actual_mixed_curve_new_exceptional_exponent_evolution (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hH : IsSNCDivisor n [H]) (hdense : N ⊆ closure (N \ H))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∈ C) :
    divExpAlong n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))) (π ⁻¹' C) z+
      (if π z ∈ H then 1 else 0)=ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let D := π ⁻¹' C
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  have hw0 : (geometricTemplate N []).IsWellFormed :=
    ⟨hN,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hC : (geometricTemplate N []).IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact hCN
  have hwNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw0 hC hπ
  have hD : IsSNCDivisor n [D] := hwNew.isSNCDivisor
  have hTrans : IsTransverse n N' [D] := hwNew.isTransverse
  obtain ⟨hN',_hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_mixed_discrete_centre_whole_strict_trace_geometry hn hN hH hdense hrC hπ hCN
  have hrNew := BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hN.1 hrN hCN hz
  have hExp := actual_curve_member_divExp_eq_ordinaryTraceOrder hn hN' hD hTrans hcI hnzI hrNew
    (0 : Fin [D].length) hzC
  change divExpAlong n N' I' D z=ordinaryTraceOrder N' I' z at hExp
  change divExpAlong n N' I' D z+_= _
  rw [hExp]
  exact actual_mixed_curve_ambient_strict_trace_order_evolution hn hN hrN hH hdense hrC hπ hCN hz hzC

/-- ONLY original curve input/ANY original TEST and its actual next admissible
step internally supply EVERY true original-member contact/exponent recurrence. -/
theorem original_curve_next_member_contact_and_exponent_evolution (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {C : Set Y} (hC : (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π) (i : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let H := strictAlong T (E.get i)
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C A.N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    ∀ z ∈ N',π z ∈ C →
      ordinaryTraceOrder N' I' z+(if π z ∈ H then 1 else 0)=
        ordinaryTraceOrder A.N (restrictOn n A.N (vanishingIdeal (n := n) H)) (π z) ∧
      divExpAlong n N' I' (π ⁻¹' C) z+(if π z ∈ H then 1 else 0)=
        ordinaryTraceOrder A.N (restrictOn n A.N (vanishingIdeal (n := n) H)) (π z) := by
  dsimp only
  let M := originalMemberProductMarked W E 1
  let A := geoTransformAlong (geometricTemplate W []) T
  let H := strictAlong T (E.get i)
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres M hInit T hT
  have hStep : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  have hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0 :=
    (original_domain_one_test_actual_discrete_centres M hInit (.step T C π hπ) hStep).2
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hCN : C ⊆ A.N := by rw [←hQN]; exact hC.subset_N
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hPure := actual_template_regular_dimension hW 1 hr T hGeom
  have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
  have hDenseI : W ⊆ closure (W \ E.get i) := by
    apply Subset.trans hdense
    apply closure_mono
    exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
  obtain ⟨hH,hDense,_hcI,_hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry
    hn hW hSingle hDenseI T hGeom hDisc
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ A.N,IsNonzeroAlongAt A.N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hDense hx
  intro z hz hzC
  have hxN : π z ∈ A.N := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
    hπ.contMDiff.continuous hwA.isClosedSubmanifold_N.1 hz
  have hNorm := HironakaSharpActualFiniteMemberProduct.ordinaryTraceOrder_restrictOn_eq
    hwA.isClosedSubmanifold_N hcH hnzH hxN
  rw [hNorm]
  exact ⟨actual_mixed_curve_ambient_strict_trace_order_evolution hn hwA.isClosedSubmanifold_N hPure
      hH hDense hrC hπ hCN hz hzC,
    actual_mixed_curve_new_exceptional_exponent_evolution hn hwA.isClosedSubmanifold_N hPure
      hH hDense hrC hπ hCN hz hzC⟩

end
end Hironaka.HironakaSharpActualMixedCurveContactEvolution
