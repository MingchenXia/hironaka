/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualTotalMonomialFactorTransport

/-! Actual old monomial transport and genuine new factor uniqueness give
WHOLE one-step TOTAL nonmonomial transport. Composite history remains next. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualTotalNonmonomialTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualTotalMonomialFactorTransport HironakaSharpActualRelativeMonomialProduct
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualControlledRelativeSaturation
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MonomialCaseAlong NonmonomialTransformAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers MarkedIdealOperationsAlong RestrictLeCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Independently actual parts and transported factors construct true new
combined monomial geometry BEFORE both real factor directions are asserted. -/
theorem actual_total_new_combined_factor_data (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) :
    let Q := nextTotalMarked N I C π
    let B := nextTotalMarked N (nonmonomialPartAlong n N I E) C π
    let A := nextTotalMarked N (monomialPartAlong n N I E) C π
    let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
    let R := nonmonomialPartAlong n Q.N B.ideal E'
    let H := (monomialPartAlong n Q.N B.ideal E').mul A.ideal
    B.ideal.IsCoherent ∧ (∀ y ∈ Q.N,IsNonzeroAlongAt Q.N B.ideal y) ∧
      H.IsCoherent ∧ (∀ y ∈ Q.N,IsNonzeroAlongAt Q.N H y) ∧ IsMonomialAlong n Q.N H E' ∧ R.IsCoherent ∧
      (∀ y ∈ Q.N,∀ i : Fin E'.length,y ∈ E'.get i → ∃ g,R.mem y g ∧
        ¬IsInSpanOnAt (n := n) Q.N ((vanishingIdeal (n := n) (E'.get i)).mem y) y g) ∧
      RestrictLe Q.N Q.ideal (R.mul H) ∧ RestrictLe Q.N (R.mul H) Q.ideal := by
  let Q := nextTotalMarked N I C π
  let B := nextTotalMarked N (nonmonomialPartAlong n N I E) C π
  let A := nextTotalMarked N (monomialPartAlong n N I E) C π
  let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  let R := nonmonomialPartAlong n Q.N B.ideal E'
  let M := monomialPartAlong n Q.N B.ideal E'
  let H := M.mul A.ideal
  obtain ⟨hcOldR,_hcOldA,_hnzOldA,_hmOldA,_hndOldR,hnzOldR,_heqOld⟩ :=
    parts_hypotheses hn (⟨N,E,I,0⟩ : MarkedIdeal n X) ⟨hN,hI,hE,hT⟩ hnz
  have hNc : IsClosedSubmanifold n Q.N := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  obtain ⟨hEc,hTc⟩ := actual_accumulated_exceptional_geometry hN hI hE hT hπ hCN hNC
  have hcB : B.ideal.IsCoherent := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    (⟨N,[],nonmonomialPartAlong n N I E,0⟩ : MarkedIdeal n X) hN hcOldR hπ hCN
  have hnzB : ∀ y ∈ Q.N,IsNonzeroAlongAt Q.N B.ideal y :=
    HironakaCoherentTransformExtension.isNonzeroAlongAt_geoTransform_without_admissibility
      (⟨N,[],nonmonomialPartAlong n N I E,0⟩ : MarkedIdeal n X) hN hcOldR hπ hCN hnzOldR
  obtain ⟨hWhole,hcA,hnzA,hmA⟩ := actual_original_parts_whole_total_factor_transport hn hN hE hT hI hnz hπ hCN hNC
  obtain ⟨hcR,hcM,hnzM,hmM,hndR,_hnzR,heqB⟩ := parts_hypotheses hn
    (⟨Q.N,E',B.ideal,0⟩ : MarkedIdeal n Y) ⟨hNc,hcB,hEc,hTc⟩ hnzB
  obtain ⟨hcH,hnzH,hmH⟩ := actual_relative_monomial_product_geometry hn hNc hEc hTc hcM hcA hnzM hnzA hmM hmA
  have hProdCoh : (B.ideal.mul A.ideal).IsCoherent := isCoherent_mul hcB hcA
  have hQprod : RestrictLe Q.N Q.ideal (B.ideal.mul A.ideal) := by
    rw [hWhole]
    exact restrictLe_restrictOn
  have hprodQ : RestrictLe Q.N (B.ideal.mul A.ideal) Q.ideal := by
    rw [hWhole]
    exact restrictLe_self_restrictOn hProdCoh
  have hAssoc : (R.mul M).mul A.ideal=R.mul H := GermIdealTotalTransform.mul_assoc hcR hcM hcA
  have hf := restrictLe_mul (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_mul hcR hcM) hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg) heqB.le (restrictLe_refl hcA)
  have hb := restrictLe_mul (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcB hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg) heqB.ge (restrictLe_refl hcA)
  change RestrictLe Q.N (B.ideal.mul A.ideal) ((R.mul M).mul A.ideal) at hf
  change RestrictLe Q.N ((R.mul M).mul A.ideal) (B.ideal.mul A.ideal) at hb
  rw [hAssoc] at hf hb
  exact ⟨hcB,hnzB,hcH,hnzH,hmH,hcR,hndR,RestrictLeCalculus.RestrictLe.trans hQprod hf,RestrictLeCalculus.RestrictLe.trans hb hprodQ⟩

/-- TRUE monomial-factor uniqueness and genuine colon normalization prove the
WHOLE one-step TOTAL nonmonomial dictionary, without a principal-ideal premise. -/
theorem actual_whole_total_nonmonomial_parts_transport (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) :
    let Q := nextTotalMarked N I C π
    let B := nextTotalMarked N (nonmonomialPartAlong n N I E) C π
    let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
    nonmonomialPartAlong n Q.N Q.ideal E'=nonmonomialPartAlong n Q.N B.ideal E' := by
  let Q := nextTotalMarked N I C π
  let B := nextTotalMarked N (nonmonomialPartAlong n N I E) C π
  let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  let R := nonmonomialPartAlong n Q.N B.ideal E'
  let H := (monomialPartAlong n Q.N B.ideal E').mul (nextTotalMarked N (monomialPartAlong n N I E) C π).ideal
  obtain ⟨hcB,hnzB,hcH,hnzH,hmH,hcR,hndR,hf,hb⟩ := actual_total_new_combined_factor_data hn hN hE hT hI hnz hπ hCN hNC
  have hNc : IsClosedSubmanifold n Q.N := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  obtain ⟨hEc,hTc⟩ := actual_accumulated_exceptional_geometry hN hI hE hT hπ hCN hNC
  have hM := monomialPartAlong_eq_of_factor hn hNc hEc hTc hcR hcH hndR hf hb
  have hLo : R.Le (nonmonomialPartAlong n Q.N Q.ideal E') :=
    le_nonmonomialPartAlong_of_factor hNc.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcR hg)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcH hg) hmH hM hb
  have hUp : RestrictLe Q.N (nonmonomialPartAlong n Q.N Q.ideal E') R :=
    restrictLe_nonmonomialPartAlong_of_factor hn hNc hEc hTc hcR hcH hnzH hmH hM hf
  have hcMB := isCoherent_monomialPartAlong hn hNc hEc hTc hcB hnzB
  ext y g
  constructor
  · intro hg
    by_cases hy : y ∈ Q.N
    · exact (restrictOn_colonAlong_mem_iff Q.N B.ideal (monomialPartAlong n Q.N B.ideal E')
        (fun _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcMB ha) g).mp
        ⟨hg.1,hUp y hy g hg⟩
    · refine ⟨hg.1,fun a ha => ?_⟩
      exact restrictOn_eq_top_of_disjoint (W := Q.N) (𝔞 := B.ideal) hNc.1.isOpen_compl hy (by simp) (ha.1.mul hg.1)
  · exact fun hg => hLo y g hg

end
end Hironaka.HironakaSharpActualTotalNonmonomialTransport
