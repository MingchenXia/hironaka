/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual

/-! EXISTING literal ambient strictAlong traces, independent chronological
STRICT ideals and genuine whole accumulated factor dictionaries. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualChronologicalAmbientTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalNoOldFactor HironakaSharpActualTotalAccumulatedResidual
  HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualTotalNonmonomialTransport HironakaSharpActualCompositeTotalResidual
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaOneDimensionalCanonicalSuperlevels
  RelativePrincipalizationSpan RestrictedIdealExtension NormalCrossings NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal MonomialPartAlong DivisorExponentAlong
  RestrictedIdealWeight RestrictedIdealQuotient IdealWeightPowers MarkedIdealOperationsAlong
  InvertibleIdealQuotient NonmonomialTransformAlong HomogenizedGlueingTower GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Literal geometric condition on the ACTUAL finite centres, independent of
any proposed ideal, invariant, residual or factor history. -/
def actualDiscreteCentres : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => actualDiscreteCentres T ∧ ∀ x ∈ C,RegularAtDim (n := n) C x 0

/-- ONLY original dimension-one TEST data internally produce EVERY genuine
regular-zero centre, including all actual empty steps. -/
theorem original_domain_one_test_actual_discrete_centres (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T → actualDiscreteCentres T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    refine ⟨original_domain_one_test_actual_discrete_centres M hM T hT.1,?_⟩
    have hCur := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT.1
    have hCos := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
      hCur.isWellFormed.isCoherent hCur.isWellFormed.isClosedSubmanifold_N hCur.one_le_d
    have hDim := dimLE_cosupport_of_isInvDomain hCur
    intro x hx
    have hxCos := hT.2.2.1 hx
    have hxReg := regularAtDim_zero_of_analytic_dimLE_zero hCos hDim hxCos
    obtain ⟨O,hO,hxO,hIso⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hxReg
    have hEq : (geoTransformAlong M T).cosupp ∩ O=C ∩ O := by
      apply Subset.antisymm
      · intro y hy
        exact ⟨by rw [hIso hy];exact hx,hy.2⟩
      · exact fun _ hy => ⟨hT.2.2.1 hy.1,hy.2⟩
    exact RegularPointDimension.regularAtDim_of_inter_eq hO hxO hEq hxReg

/-- Original true density and actual discrete centres internally construct
all genuine literal ambient strict-member trace geometry at EVERY position. -/
theorem actual_finite_ambient_strict_trace_geometry (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T → actualDiscreteCentres T →
      let A := geoTransformAlong (geometricTemplate W []) T
      let HT := strictAlong T H
      let I := restrictOn n A.N (vanishingIdeal (n := n) HT)
      IsSNCDivisor n [HT] ∧ A.N ⊆ closure (A.N \ HT) ∧ I.IsCoherent ∧
        (∀ y ∈ A.N,IsNonzeroAlongAt A.N I y) ∧
        ∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,I.mem y g ↔
          HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g
  | _, .refl, _, _ => by
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length))
    refine ⟨hH,hdense,isCoherent_restrictOn hcH (VanishingIdealCoherent.isCoherent_vanishingIdeal hW),?_,?_⟩
    · intro x hx
      obtain ⟨g,hg,hfreq⟩ := HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
      exact ⟨g,le_restrictOn hcH x g hg,hfreq⟩
    · intro x _hx
      obtain ⟨f,hf,hgen⟩ := exists_originalMember_principal hn hH (H := H) (by simp) x
      exact ⟨f,hf,fun g => and_congr_right fun _ => restricted_span_iff_principal hf hgen g⟩
  | _, .step T C π hπ, hT, hD => by
    obtain ⟨hHT,hDense,_hcI,_hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry hn hW hH hdense T hT.1 hD.1
    have hw0 : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT.1
    obtain ⟨_hN,hAmbient,hcNew,hnzNew,hDenseNew,hPrNew⟩ :=
      actual_mixed_discrete_centre_whole_strict_trace_geometry hn hwA.isClosedSubmanifold_N hHT hDense hD.2 hπ hT.2.subset_N
    have hSingle := isSNCDivisor_of_sublist hAmbient (show [BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T H)].Sublist
      [BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T H),π ⁻¹' C] from by simp)
    exact ⟨hSingle,hDenseNew,hcNew,hnzNew,hPrNew⟩

/-- Literal true ambient strict traces have the independently chronological
STRICT residual along the WHOLE actual accumulated exceptional list. -/
theorem actual_finite_ambient_trace_nonmonomial_eq_chronological (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T → actualDiscreteCentres T →
      let A := geoTransformAlong (geometricTemplate W []) T
      nonmonomialPartAlong n A.N (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T H))) A.E=
        (chronologicalMarked (originalRelativeMemberMarked W H) T).ideal
  | _, .refl, _, _ => by
    change nonmonomialPartAlong n W (restrictOn n W (vanishingIdeal (n := n) H)) []=
      restrictOn n W (vanishingIdeal (n := n) H)
    rw [nonmonomialPartAlong_nil_eq_restrictOn]
    ext x g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  | _, .step T C π hπ, hT, hD => by
    let A := geoTransformAlong (geometricTemplate W []) T
    let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T H))
    let J := chronologicalMarked (originalRelativeMemberMarked W H) T
    have hw0 : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT.1
    obtain ⟨hHT,hDense,hcI,hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry hn hW hH hdense T hT.1 hD.1
    have hCN : C ⊆ A.N := hT.2.subset_N
    have hNC : HasNormalCrossings n C A.E := hT.2.2.2
    obtain ⟨_hENew,_hTNew,hTraceRaw⟩ := actual_mixed_discrete_accumulated_trace_nonmonomial_eq_total hn
      hwA.isClosedSubmanifold_N hwA.isSNCDivisor hwA.isTransverse hHT hDense hD.2 hπ hCN
    have hStep := actual_whole_total_nonmonomial_parts_transport hn hwA.isClosedSubmanifold_N hwA.isSNCDivisor
      hwA.isTransverse hcI hnzI hπ hCN hNC
    have hIH := actual_finite_ambient_trace_nonmonomial_eq_chronological hn hW hH hdense T hT.1 hD.1
    change nonmonomialPartAlong n A.N I A.E=J.ideal at hIH
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
      (nextTotalMarked A.N I C π).ideal (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=
      nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
        (nextTotalMarked A.N (nonmonomialPartAlong n A.N I A.E) C π).ideal
        (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hStep
    rw [hIH] at hStep
    have hRaw := HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
      (⟨A.N,[],I,0⟩ : MarkedIdeal n _) rfl C π
    change (nextTotalMarked A.N I C π).ideal=restrictOn n
      (BlowupStrictSubmanifold.geoStrictTransform π C A.N) (GermIdeal.pullback (m := n) π I) at hRaw
    have hNewN := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hwA.isClosedSubmanifold_N hCN
    have hHcur : IsClosedSubmanifold n (strictAlong T H) := MonomialPart.isClosedSubmanifold_get hn hHT (0 : Fin [strictAlong T H].length)
    have hcHcur := VanishingIdealCoherent.isCoherent_vanishingIdeal hHcur
    have hNorm := actual_normalized_pullback_restrictOn hwA.isClosedSubmanifold_N hNewN.1 hcHcur hπ.contMDiff
      (fun y hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwA.isClosedSubmanifold_N.1 hy)
    rw [hRaw,hNorm] at hStep
    have hDenseSingle : W ⊆ closure (W \ ⋃ K ∈ [H],K) := by simpa using hdense
    obtain ⟨hJN,hJE,_hJd,hwJ,hnzJ,hprJ⟩ := original_members_actual_finite_chronological_geometry
      hn hW hH hDenseSingle (0 : Fin [H].length) T hT.1
    change J.N=A.N at hJN
    change J.E=A.E at hJE
    have hCJ : C ⊆ J.N := by rw [hJN]; exact hCN
    have hNCJ : HasNormalCrossings n C J.E := by rw [hJE]; exact hNC
    have hNo := original_members_actual_finite_chronological_no_exceptional_factor hn hW hH hDenseSingle
      (0 : Fin [H].length) T hT.1
    have hNext := nextTotal_accumulated_nonmonomial_eq_nextStrict hn hwJ.isClosedSubmanifold_N hwJ.isSNCDivisor
      hwJ.isTransverse hwJ.isCoherent hnzJ hprJ hπ hCJ hNCJ hNo
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C J.N)
      (nextTotalMarked J.N J.ideal C π).ideal (J.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=
      nextRelativeStrict J.N J.ideal C π at hNext
    rw [hJN,hJE] at hNext
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T H))))
      (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=nextRelativeStrict J.N J.ideal C π
    rw [hJN]
    exact hTraceRaw.trans (hStep.trans hNext)

/-- ONLY original smooth curve product tests internally supply every actual
history condition and produce TRUE whole ambient member I_i=D_i*J_i. -/
theorem original_curve_history_true_ambient_member_factor_dictionary (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) (i : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
    let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let D := monomialPartAlong n A.N I A.E
    I.IsCoherent ∧ (∀ y ∈ A.N,IsNonzeroAlongAt A.N I y) ∧
      D.IsCoherent ∧ (∀ y ∈ A.N,IsNonzeroAlongAt A.N D y) ∧ IsMonomialAlong n A.N D A.E ∧
      nonmonomialPartAlong n A.N I A.E=J ∧ I=restrictOn n A.N (D.mul J) := by
  let M := originalMemberProductMarked W E 1
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hDiscrete := original_domain_one_test_actual_discrete_centres M hInit T hT
  have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
  have hDenseI : W ⊆ closure (W \ E.get i) := by
    apply Subset.trans hdense
    apply closure_mono
    intro x hx
    refine ⟨hx.1,fun hxI => ?_⟩
    exact hx.2 (Set.mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hxI⟩)
  obtain ⟨_hHT,_hDense,hcI,hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDiscrete
  have hNm := actual_finite_ambient_trace_nonmonomial_eq_chronological hn hW hSingle hDenseI T hGeom hDiscrete
  let A := geoTransformAlong (geometricTemplate W []) T
  let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  obtain ⟨_hcJ,hcD,hnzD,hmD,_hNo,_hnzJ,hFactor⟩ := parts_hypotheses hn
    (⟨A.N,A.E,I,0⟩ : MarkedIdeal n Y) ⟨hwA.isClosedSubmanifold_N,hcI,hwA.isSNCDivisor,hwA.isTransverse⟩ hnzI
  have hWhole := restrictOn_eq_of_restrictLe hwA.isClosedSubmanifold_N.1 hFactor.le hFactor.ge
  change restrictOn n A.N I=restrictOn n A.N ((nonmonomialPartAlong n A.N I A.E).mul (monomialPartAlong n A.N I A.E)) at hWhole
  rw [hNm,RestrictLeCalculus.mul_comm' _ (monomialPartAlong n A.N I A.E)] at hWhole
  have hNorm : restrictOn n A.N I=I := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  exact ⟨hcI,hnzI,hcD,hnzD,hmD,hNm,hNorm.symm.trans hWhole⟩

end
end Hironaka.HironakaSharpActualChronologicalAmbientTrace
