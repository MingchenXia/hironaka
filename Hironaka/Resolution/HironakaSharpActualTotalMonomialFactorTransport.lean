/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualRelativeMonomialProduct

/-! Genuine old monomial factor transport and WHOLE actual original-parts
TOTAL factor equality BEFORE composite residual uniqueness. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualTotalMonomialFactorTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualControlledRelativeSaturation
  HironakaSharpOriginalFirstMemberExceptionalFactor RelativePrincipalizationSpan
  RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient GermIdealOrder RestrictLeCalculus MarkedIdealOperationsAlong
  MonomialPartAlong DivisorExponentAlong NormalCrossings MonomialCaseAlong MonomialStepAlong
  NonmonomialStepAlong MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem actual_zero_mark_admissible {N C : Set X} {E : List (Set X)} {I : GermIdeal n X}
    (hI : I.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hNC : HasNormalCrossings n C E) : (⟨N,E,I,0⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
  refine ⟨hπ.1,?_,hNC⟩
  change C ⊆ cosupport n N I 0
  rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  exact hCN

private theorem actual_monomialFactor_zero_eq_total {N C : Set X} {E : List (Set X)} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) :
    monomialFactor n π C N E I 0 0=(nextTotalMarked N I C π).ideal := by
  have hC := actual_zero_mark_admissible hI hπ hCN hNC
  have hc := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hI hC hπ
  unfold monomialFactor
  simp only [Nat.sub_self,idealPow_zero]
  rw [BlowupControlledTransform.unitIdeal_mul hc]
  rfl

/-- REAL whole-boundary NC transports an ACTUAL monomial factor to genuine
coherent nonzero monomial TOTAL on the ENTIRE new ordered boundary. -/
theorem nextTotal_actual_monomial_geometry (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hm : IsMonomialAlong n N I E) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) :
    let Q := nextTotalMarked N I C π
    Q.ideal.IsCoherent ∧ (∀ y ∈ Q.N,IsNonzeroAlongAt Q.N Q.ideal y) ∧
      IsMonomialAlong n Q.N Q.ideal (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  have hC := actual_zero_mark_admissible hI hπ hCN hNC
  have hwQ := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    (show (⟨N,E,I,0⟩ : MarkedIdeal n X).IsWellFormed from ⟨hN,hI,hE,hT⟩) hC hπ
  have hFactor := actual_monomialFactor_zero_eq_total hN hI hπ hCN hNC
  have hloc : ∀ y ∈ (nextTotalMarked N I C π).N,IsPrincipalMonomialAlongAt n
      (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal
      (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) y := by
    intro y hy
    obtain ⟨b,hb⟩ := isPrincipalAlongAt_monomialFactor hn hπ hN hE hT hI hnz hm
      (o := 0) (d := 0) hNC hC.2.1 hy
    have hp := hb.isPrincipalMonomialAlongAt
    rw [hFactor] at hp
    exact hp
  exact ⟨hwQ.isCoherent,isNonzeroAlongAt_and_isMonomialAlong_of_principal hn
    hwQ.isClosedSubmanifold_N hwQ.isSNCDivisor hwQ.isTransverse hwQ.isCoherent hloc⟩

/-- ONLY genuine old parts supply the WHOLE actual TOTAL factor dictionary and
true transported monomial geometry, before any composite residual claim. -/
theorem actual_original_parts_whole_total_factor_transport (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) :
    let R := nonmonomialPartAlong n N I E
    let A := monomialPartAlong n N I E
    let Q := nextTotalMarked N I C π
    let QR := nextTotalMarked N R C π
    let QA := nextTotalMarked N A C π
    Q.ideal=restrictOn n Q.N (QR.ideal.mul QA.ideal) ∧
      QA.ideal.IsCoherent ∧ (∀ y ∈ QA.N,IsNonzeroAlongAt QA.N QA.ideal y) ∧
        IsMonomialAlong n QA.N QA.ideal (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  let R := nonmonomialPartAlong n N I E
  let A := monomialPartAlong n N I E
  obtain ⟨hcR,hcA,hnzA,hmA,_hndR,_hnzR,heq⟩ := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨N,E,I,0⟩ : MarkedIdeal n X) ⟨hN,hI,hE,hT⟩ hnz
  have hCp := actual_zero_mark_admissible (isCoherent_mul hcR hcA) hπ hCN hNC
  have hCR := actual_zero_mark_admissible hcR hπ hCN hNC
  have hCA := actual_zero_mark_admissible hcA hπ hCN hNC
  have hTransform := heq.geoTransform_eq hN.1 hI (isCoherent_mul hcR hcA) (C := C) hπ.contMDiff
  have hIdeal := congrArg (fun M : MarkedIdeal n Y => M.ideal) hTransform
  change (nextTotalMarked N I C π).ideal=(nextTotalMarked N (R.mul A) C π).ideal at hIdeal
  obtain ⟨hf,hb⟩ := restrictLe_geoTransform_mul hπ hN E hcR hcA (o := 0) (d := 0) hCR hCA hCp
  have hFactor := actual_monomialFactor_zero_eq_total hN hcA hπ hCN hNC
  rw [hFactor] at hf hb
  change RestrictLe (nextTotalMarked N I C π).N (nextTotalMarked N (R.mul A) C π).ideal
    ((nextTotalMarked N R C π).ideal.mul (nextTotalMarked N A C π).ideal) at hf
  change RestrictLe (nextTotalMarked N I C π).N
    ((nextTotalMarked N R C π).ideal.mul (nextTotalMarked N A C π).ideal) (nextTotalMarked N (R.mul A) C π).ideal at hb
  rw [← hIdeal] at hf hb
  have hWhole := restrictOn_eq_of_restrictLe isClosed_closure hf hb
  have hNorm : restrictOn n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal=
      (nextTotalMarked N I C π).ideal := by
    ext y g
    exact restrictOn_colonAlong_mem_iff _ _ _ (fun _ ha => ha) g
  change restrictOn n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal=
    restrictOn n (nextTotalMarked N I C π).N ((nextTotalMarked N R C π).ideal.mul (nextTotalMarked N A C π).ideal) at hWhole
  rw [hNorm] at hWhole
  exact ⟨hWhole,nextTotal_actual_monomial_geometry hn hN hE hT hcA hnzA hmA hπ hCN hNC⟩

end
end Hironaka.HironakaSharpActualTotalMonomialFactorTransport
