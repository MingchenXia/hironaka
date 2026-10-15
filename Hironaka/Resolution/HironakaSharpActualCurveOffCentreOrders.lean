/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveControlledOrderShift

/-! Actual mark-independent controlled germs, ordinary orders and true
ambient contact budget off centre. No invariant rebasing or driver certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveOffCentreOrders
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveControlledOrderShift HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualChronologicalAmbientTrace
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry HironakaSharpActualCurveAmbientContactBudget
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualOriginalControlledHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  NormalCrossings NormalCrossingsComparison MarkedIdeals MarkedIdeals.MarkedIdeal
  MonomialPartAlong DivisorExponentAlong IdealWeightPowers GermIdealOrder
  InvertibleIdealQuotient HadamardBridge IdealOrderArithmetic BlowupControlledTransform HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The ACTUAL unit lies in every genuine denominator power; whole controlled
membership is therefore mark-independent off the actual centre. -/
theorem actual_controlled_germ_iff_normalized_raw_off_centre (M : MarkedIdeal n X)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y} (hzC : π z ∉ C) (g : Y → ℂ) :
    (M.geoTransform C π).ideal.mem z g ↔
      (restrictOn n (M.geoTransform C π).N (GermIdeal.pullback (m := n) π M.ideal)).mem z g := by
  have h1 := one_mem_idealPow (n := n)
    (one_mem_pullback_vanishingIdeal (n := n) (π := π) hzC hπ.1.1) M.d
  have hcDen := GermIdealPullbackCalculus.isCoherent_idealPow
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) M.d
  constructor
  · intro hg
    change (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C M.N)
      (GermIdeal.pullback (m := n) π M.ideal)).mem z g
    simpa only [Pi.one_apply,one_mul] using hg.2 (1 : Y → ℂ) h1
  · intro hg
    refine ⟨hg.1,fun a ha => ?_⟩
    exact restrictOn_mul_left (GermIdeal.IsCoherent.holomorphicAt_mem hcDen ha) hg

/-- Mark-q actual off-centre cosupport is used WITHOUT claiming candidate
admissibility, after true mark-independent controlled germs were proved. -/
theorem actual_controlled_cosupport_off_centre_iff (M : MarkedIdeal n X)
    (hN : IsClosed M.N) (hcI : M.ideal.IsCoherent)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y} (hzC : π z ∉ C) (q : ℕ) :
    z ∈ cosupport n (M.geoTransform C π).N (M.geoTransform C π).ideal q ↔
      π z ∈ cosupport n M.N M.ideal q := by
  let J : MarkedIdeal n X := ⟨M.N,M.E,M.ideal,q⟩
  have hMem : ∀ g,(M.geoTransform C π).ideal.mem z g ↔ (J.geoTransform C π).ideal.mem z g :=
    fun g => (actual_controlled_germ_iff_normalized_raw_off_centre M hπ hzC g).trans
      (actual_controlled_germ_iff_normalized_raw_off_centre J hπ hzC g).symm
  have hCos : z ∈ cosupport n (M.geoTransform C π).N (M.geoTransform C π).ideal q ↔
      z ∈ (J.geoTransform C π).cosupp := by
    constructor
    · rintro ⟨hz,hOrder⟩
      exact ⟨hz,fun g hg => hOrder g ((hMem g).mpr hg)⟩
    · rintro ⟨hz,hOrder⟩
      exact ⟨hz,fun g hg => hOrder g ((hMem g).mp hg)⟩
  exact hCos.trans (TransformOffCentre.mem_cosupp_geoTransform_iff J hN
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg) hπ hzC)

/-- Actual ordinary orders compare via BOTH independently proved whole
threshold directions; no curve, canonicality or order equality premise. -/
theorem actual_controlled_ordinary_order_off_centre (M : MarkedIdeal n X) (hw : M.IsWellFormed)
    (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : z ∈ (M.geoTransform C π).N) (hzC : π z ∉ C) :
    ordinaryTraceOrder (M.geoTransform C π).N (M.geoTransform C π).ideal z=
      ordinaryTraceOrder M.N M.ideal (π z) := by
  have hwNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  have hnzNew := isNonzeroAlongAt_geoTransform_without_admissibility M hw.isClosedSubmanifold_N hw.isCoherent hπ hC.subset_N hnz
  have hxN := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hw.isClosedSubmanifold_N.1 hz
  have hq := actual_controlled_cosupport_off_centre_iff M hw.isClosedSubmanifold_N.1 hw.isCoherent hπ hzC
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hw.isClosedSubmanifold_N hw.isCoherent hnz hxN _).mp
    exact (hq _).mp ((ordinaryTraceOrder_cosupport_iff hwNew.isClosedSubmanifold_N hwNew.isCoherent hnzNew hz _).mpr le_rfl)
  · apply (ordinaryTraceOrder_cosupport_iff hwNew.isClosedSubmanifold_N hwNew.isCoherent hnzNew hz _).mp
    exact (hq _).mpr ((ordinaryTraceOrder_cosupport_iff hw.isClosedSubmanifold_N hw.isCoherent hnz hxN _).mpr le_rfl)

/-- Genuine mixed-centre whole residual comparison BEFORE actual unit removal
off NEW exceptionals gives TRUE ambient contact ordinary-order transport. -/
theorem actual_mixed_discrete_ambient_trace_order_off_centre (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∉ C) :
    ordinaryTraceOrder (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))) z=
      ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  have hw0 : M0.IsWellFormed := ⟨hN,hcH,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hC0 : M0.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (vanishingIdeal (n := n) H) 0
    have hholH : ∀ x g,(vanishingIdeal (n := n) H).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
    rw [cosupport_zero hholH]
    exact hCN
  have hRaw := geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  change (M0.geoTransform C π).ideal=P at hRaw
  have hcP : P.IsCoherent := by
    rw [←hRaw]
    exact (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw0 hC0 hπ).isCoherent
  obtain ⟨_hN',_hAmbient,hcI,_hnzI,_hDense,_hPr⟩ :=
    actual_mixed_discrete_centre_whole_strict_trace_geometry hn hN hH hdense hrC hπ hCN
  obtain ⟨_hE,_hT,hEq⟩ := actual_mixed_discrete_accumulated_trace_nonmonomial_eq_total hn hN
    isSNCDivisor_nil (isTransverse_nil_of_isClosedSubmanifold hN) hH hdense hrC hπ hCN
  change nonmonomialPartAlong n N' I' [π ⁻¹' C]=nonmonomialPartAlong n N' P [π ⁻¹' C] at hEq
  have hOff : z ∉ ⋃ D ∈ [π ⁻¹' C],D := by simpa using hzC
  have hMem : ∀ g,I'.mem z g ↔ P.mem z g := by
    intro g
    have hNm : (nonmonomialPartAlong n N' I' [π ⁻¹' C]).mem z g ↔
        (nonmonomialPartAlong n N' P [π ⁻¹' C]).mem z g := by rw [hEq]
    exact (actual_normalized_nonmonomial_off_family_iff
      (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)) hOff g).symm.trans
      (hNm.trans (actual_normalized_nonmonomial_off_family_iff
        (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) hOff g))
  have hOrd : ordinaryTraceOrder N' I' z=ordinaryTraceOrder N' P z := by
    apply NonmonomialOrderLocal.nmOrd_congr
    intro q
    rw [ordGe_ordinaryTraceMarked_eq_cosupport N' I' hcI,ordGe_ordinaryTraceMarked_eq_cosupport N' P hcP]
    constructor
    · rintro ⟨hzN,hOrder⟩
      exact ⟨hzN,fun g hg => hOrder g ((hMem g).mpr hg)⟩
    · rintro ⟨hzN,hOrder⟩
      exact ⟨hzN,fun g hg => hOrder g ((hMem g).mp hg)⟩
  have hRawOrd := actual_controlled_ordinary_order_off_centre M0 hw0 hnzH hC0 hπ hz hzC
  rw [hRaw] at hRawOrd
  exact hOrd.trans hRawOrd

/-- ONLY original curve inputs construct EACH real current ambient strict
member before summing true ordinary contact equalities off centre. -/
theorem original_curve_actual_contact_budget_off_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {C : Set Y} (hC : (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : z ∈ (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N)
    (hzC : π z ∉ C) :
    actualAmbientContactBudget W E (.step T C π hπ) z=actualAmbientContactBudget W E T (π z) := by
  let M := originalMemberProductMarked W E 1
  let A := geoTransformAlong (geometricTemplate W []) T
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres M hInit T hT
  have hStep : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  have hrC := (original_domain_one_test_actual_discrete_centres M hInit (.step T C π hπ) hStep).2
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hCN : C ⊆ A.N := by rw [←hQN];exact hC.subset_N
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hxN : π z ∈ A.N := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
    hπ.contMDiff.continuous hwA.isClosedSubmanifold_N.1 hz
  unfold actualAmbientContactBudget
  apply Finset.sum_congr rfl
  intro i _hi
  have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
  have hDenseI : W ⊆ closure (W \ E.get i) := by
    apply Subset.trans hdense
    apply closure_mono
    exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
  obtain ⟨hHT,hDense,_hcI,_hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc
  have hHc : IsClosedSubmanifold n (strictAlong T (E.get i)) :=
    MonomialPart.isClosedSubmanifold_get hn hHT (0 : Fin [strictAlong T (E.get i)].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ A.N,IsNonzeroAlongAt A.N (vanishingIdeal (n := n) (strictAlong T (E.get i))) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hHT hDense hx
  rw [HironakaSharpActualFiniteMemberProduct.ordinaryTraceOrder_restrictOn_eq hwA.isClosedSubmanifold_N hcH hnzH hxN]
  exact actual_mixed_discrete_ambient_trace_order_off_centre hn hwA.isClosedSubmanifold_N hHT hDense hrC hπ hCN hz hzC

end
end Hironaka.HironakaSharpActualCurveOffCentreOrders
