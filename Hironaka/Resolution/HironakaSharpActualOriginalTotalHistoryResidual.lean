/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualTotalNonmonomialTransport

/-! Independently actual original mark-zero TOTAL histories have whole
ALL-accumulated residual equal to independently chronological NEW saturation.
Literal composite-projection raw pullback and original invariant remain next. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualOriginalTotalHistoryResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualTotalNonmonomialTransport HironakaSharpActualTotalAccumulatedResidual
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualChronologicalStrictStep HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual candidate coherence/nonzero precedes genuine whole raw-record
well-formedness on the independently actual template carrier and whole list. -/
theorem raw_history_actual_geometry (M : MarkedIdeal n X) (hw : M.IsWellFormed)
    (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate M.N M.E) T) :
    (geoTransformAlong M T).IsWellFormed ∧
      ∀ y ∈ (geoTransformAlong M T).N,IsNonzeroAlongAt (geoTransformAlong M T).N (geoTransformAlong M T).ideal y := by
  have hW : (geometricTemplate M.N M.E).IsWellFormed :=
    ⟨hw.isClosedSubmanifold_N,isCoherent_unitIdeal,hw.isSNCDivisor,hw.isTransverse⟩
  have hWT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hW T hT
  obtain ⟨hNc,hIc⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier
    hw.isClosedSubmanifold_N hw.isCoherent (𝔪 := geometricTemplate M.N M.E) rfl T hT
  have hN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate M.N M.E) rfl T
  have hE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate M.N M.E) rfl T
  refine ⟨⟨hNc,hIc,?_,?_⟩,?_⟩
  · rw [hE]; exact hWT.isSNCDivisor
  · rw [hN,hE]; exact hWT.isTransverse
  · exact isNonzeroAlongAt_geoTransformAlong_sameCarrier hw.isClosedSubmanifold_N hw.isCoherent
      (𝔪 := geometricTemplate M.N M.E) rfl hnz T hT

private theorem nil_nonmonomial_restricted (N : Set X) (I : GermIdeal n X) :
    nonmonomialPartAlong n N (restrictOn n N I) []=restrictOn n N I := by
  rw [HironakaSharpOriginalProductTraceOrder.nonmonomialPartAlong_nil_eq_restrictOn]
  ext x g
  constructor
  · intro hg
    exact ⟨hg.1,IsInSpanOnAt.trans (fun s hs => hs.2) hg.2⟩
  · intro hg
    exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩

private theorem zero_transform_ideal_eq (M : MarkedIdeal n X) (hm : M.d=0)
    {Y : CMfd.{u} n} (C : Set X) (π : Y → X) :
    (M.geoTransform C π).ideal=(nextTotalMarked M.N M.ideal C π).ideal := by
  change colonAlong n _ _ (idealPow _ M.d)=colonAlong n _ _ (idealPow _ 0)
  rw [hm]

/-- ONLY genuine original member/density geometry and actual template history
identify the WHOLE original mark-zero history residual with chronological J. -/
theorem original_member_total_history_residual_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T →
      let M := originalRelativeMemberMarked W (E.get i)
      let Q := geoTransformAlong M T
      nonmonomialPartAlong n Q.N Q.ideal Q.E=(chronologicalMarked M T).ideal
  | _, .refl, _ => nil_nonmonomial_restricted W _
  | _, .step T C π hπ, hT => by
    let M := originalRelativeMemberMarked W (E.get i)
    let Q := geoTransformAlong M T
    let A := chronologicalMarked M T
    obtain ⟨_hN0,_hE0,_hm0,hw0,hnz0,_hpr0⟩ := original_members_actual_finite_chronological_geometry
      hn hW hE hdense i (.refl : BlowupTower X X) trivial
    obtain ⟨hwQ,hnzQ⟩ := raw_history_actual_geometry M hw0 hnz0 T hT.1
    obtain ⟨hAN,hAE,_hAd,hwA,hnzA,hprA⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT.1
    have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hQE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hQA : Q.N=A.N := hQN.trans hAN.symm
    have hQEA : Q.E=A.E := hQE.trans hAE.symm
    have hCN : C ⊆ Q.N := by rw [hQN]; exact hT.2.subset_N
    have hNC : HasNormalCrossings n C Q.E := by rw [hQE]; exact hT.2.2.2
    have hCNA : C ⊆ A.N := by rw [←hQA]; exact hCN
    have hNCA : HasNormalCrossings n C A.E := by rw [←hQEA]; exact hNC
    have hStep := actual_whole_total_nonmonomial_parts_transport hn hwQ.isClosedSubmanifold_N hwQ.isSNCDivisor
      hwQ.isTransverse hwQ.isCoherent hnzQ hπ hCN hNC
    have hIH := original_member_total_history_residual_eq hn hW hE hdense i T hT.1
    change nonmonomialPartAlong n Q.N Q.ideal Q.E=A.ideal at hIH
    change nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N (nextTotalMarked Q.N Q.ideal C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N
        (nextTotalMarked Q.N (nonmonomialPartAlong n Q.N Q.ideal Q.E) C π).ideal
        (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hStep
    rw [hIH,hQA,hQEA] at hStep
    have hnd := original_members_actual_finite_chronological_no_exceptional_factor hn hW hE hdense i T hT.1
    have hNext := nextTotal_accumulated_nonmonomial_eq_nextStrict hn hwA.isClosedSubmanifold_N hwA.isSNCDivisor
      hwA.isTransverse hwA.isCoherent hnzA hprA hπ hCNA hNCA hnd
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N) (Q.geoTransform C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=nextRelativeStrict A.N A.ideal C π
    rw [zero_transform_ideal_eq Q (by rw [d_geoTransformAlong]; rfl) C π,hQA,hQEA]
    exact hStep.trans hNext

end
end Hironaka.HironakaSharpActualOriginalTotalHistoryResidual
