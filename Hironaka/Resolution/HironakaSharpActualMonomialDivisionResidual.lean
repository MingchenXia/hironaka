/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCompositeProductResidual

/-! Genuine monomial denominator division preserves WHOLE intrinsic residuals.
Actual quotient geometry and true factorization precede intrinsic uniqueness. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualMonomialDivisionResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCompositeProductResidual HironakaSharpActualRelativeMonomialProduct
  HironakaSharpActualControlledRelativeSaturation HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberExceptionalFactor
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient RestrictLeCalculus
  MonomialCaseAlong NonmonomialTransformAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine relative-colon inversion constructs an actual combined monomial
factor BEFORE true uniqueness; no principal numerator or factor certificate. -/
theorem actual_monomial_division_nonmonomial_eq (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I A : GermIdeal n X} (hI : I.IsCoherent) (hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hcA : A.IsCoherent) (hnzA : ∀ x ∈ N,IsNonzeroAlongAt N A x)
    (hmA : IsMonomialAlong n N A E) (hinvA : IsInvertibleAlong n N A) (hdiv : RestrictLe N I A) :
    nonmonomialPartAlong n N I E=nonmonomialPartAlong n N (colonAlong n N I A) E := by
  let J := colonAlong n N I A
  let R := nonmonomialPartAlong n N J E
  let MJ := monomialPartAlong n N J E
  let H := A.mul MJ
  have hcN := VanishingIdealCoherent.isCoherent_vanishingIdeal hN
  have hcJ : J.IsCoherent := isCoherent_colonAlong hN.1 hI hcN hcA hinvA hdiv
  have hIJ : I.Le J := by
    intro x g hg
    exact ⟨RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg,
      fun a ha => restrictOn_mul_left (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA ha)
        (le_restrictOn hI x g hg)⟩
  have hnzJ : ∀ x ∈ N,IsNonzeroAlongAt N J x := by
    intro x hx
    obtain ⟨g,hg,hfreq⟩ := hnzI x hx
    exact ⟨g,hIJ x g hg,hfreq⟩
  obtain ⟨hcR,hcMJ,hnzMJ,hmMJ,hndR,_hnzR,heqJ⟩ := parts_hypotheses hn
    (⟨N,E,J,0⟩ : MarkedIdeal n X) ⟨hN,hcJ,hE,hT⟩ hnzJ
  obtain ⟨hcH,hnzH,hmH⟩ := actual_relative_monomial_product_geometry hn hN hE hT hcA hcMJ hnzA hnzMJ hmA hmMJ
  have hInvF : RestrictLe N I (A.mul J) := restrictLe_mul_colon hI hinvA hdiv
  have hInvB : RestrictLe N (A.mul J) I := restrictLe_mul_colon' hI hcN
  have hPerm : A.mul (R.mul MJ)=R.mul H := by
    rw [←GermIdealTotalTransform.mul_assoc hcA hcR hcMJ,mul_comm' A R,GermIdealTotalTransform.mul_assoc hcR hcA hcMJ]
  have hProdF := restrictLe_mul
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_mul hcR hcMJ) hg)
    (restrictLe_refl hcA) heqJ.le
  have hProdB := restrictLe_mul
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg)
    (restrictLe_refl hcA) heqJ.ge
  change RestrictLe N (A.mul J) (A.mul (R.mul MJ)) at hProdF
  change RestrictLe N (A.mul (R.mul MJ)) (A.mul J) at hProdB
  rw [hPerm] at hProdF hProdB
  have hf := RestrictLeCalculus.RestrictLe.trans hInvF hProdF
  have hb := RestrictLeCalculus.RestrictLe.trans hProdB hInvB
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
    · exact (restrictOn_colonAlong_mem_iff N J MJ
        (fun _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcMJ ha) g).mp ⟨hg.1,hup x hx g hg⟩
    · refine ⟨hg.1,fun a ha => ?_⟩
      exact restrictOn_eq_top_of_disjoint (W := N) (𝔞 := J) hN.1.isOpen_compl hx (by simp) (ha.1.mul hg.1)
  · exact fun hg => hlo x g hg

private theorem actual_zero_unit_total_eq_unit (N C : Set X) (E : List (Set X)) (π : Y → X) :
    ((⟨N,E,unitIdeal n X,0⟩ : MarkedIdeal n X).geoTransform C π).ideal=unitIdeal n Y := by
  rw [geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,E,unitIdeal n X,0⟩ : MarkedIdeal n X) rfl]
  ext y g
  constructor
  · exact fun hg => hg.1
  · intro hg
    have h1 : (GermIdeal.pullback (m := n) π (unitIdeal n X)).mem y (1 : Y → ℂ) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨(1 : X → ℂ),holomorphicAt_const 1,rfl⟩ (holomorphicAt_const 1))
    exact ⟨hg,⟨1,fun _ => 1,fun _ => g,fun _ => h1,fun _ => hg,
      Eventually.of_forall fun z _ => by simp⟩⟩

/-- Genuine actual unit monomialFactor at o=power,d=0 constructs the real
exceptional denominator geometry BEFORE any controlled residual assertion. -/
theorem actual_new_exceptional_power_monomial (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E) (d : ℕ) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
    let A := idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d
    A.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' A y) ∧ IsMonomialAlong n N' A E' := by
  let A := idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d
  have hcA : A.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) d
  have hnzU : ∀ x ∈ N,IsNonzeroAlongAt N (unitIdeal n X) x := by
    intro x hx
    refine ⟨1,holomorphicAt_const 1,frequently_iff.mpr ?_⟩
    intro U hU
    exact ⟨x,mem_of_mem_nhds hU,hx,one_ne_zero⟩
  have hmU : IsMonomialAlong n N (unitIdeal n X) E := by
    intro x hx g hg
    exact IsInSpanAt.restrict (isInSpanAt_self hg.1 hg.1)
  have hCU : C ⊆ cosupport n N (unitIdeal n X) (0-d) := by
    rw [Nat.zero_sub,cosupport_zero (fun _ _ hg => hg)]
    exact hCN
  have hF : NonmonomialStepAlong.monomialFactor n π C N E (unitIdeal n X) d 0=A := by
    unfold NonmonomialStepAlong.monomialFactor
    simp only [Nat.sub_zero,Nat.zero_sub]
    rw [actual_zero_unit_total_eq_unit N C E π]
    exact mul_unitIdeal hcA
  have hNc := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  obtain ⟨hEc,hTc⟩ := HironakaSharpActualChronologicalStrictStep.actual_accumulated_exceptional_geometry hN isCoherent_unitIdeal hE hT hπ hCN hNC
  have hloc : ∀ y ∈ BlowupStrictSubmanifold.geoStrictTransform π C N,
      IsPrincipalMonomialAlongAt n (BlowupStrictSubmanifold.geoStrictTransform π C N) A
        (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) y := by
    intro y hy
    obtain ⟨b,hb⟩ := NonmonomialStepAlong.isPrincipalAlongAt_monomialFactor hn hπ hN hE hT isCoherent_unitIdeal hnzU hmU
      (o := d) (d := 0) hNC hCU hy
    have hp := hb.isPrincipalMonomialAlongAt
    rw [hF] at hp
    exact hp
  exact ⟨hcA,isNonzeroAlongAt_and_isMonomialAlong_of_principal hn hNc hEc hTc hcA hloc⟩

private theorem restrictOn_idempotent (N : Set Y) (I : GermIdeal n Y) :
    restrictOn n N (restrictOn n N I)=restrictOn n N I := by
  ext y g
  exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun s hs => hs.2) hg.2⟩,
    fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩

/-- ONLY original genuine marked geometry/admissibility and SAME actual map
produce the WHOLE accumulated controlled versus TOTAL residual dictionary. -/
theorem actual_geoTransform_nonmonomial_eq_total (hn : 0 < n) (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    let Q := nextTotalMarked M.N M.ideal C π
    nonmonomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).E=
      nonmonomialPartAlong n Q.N Q.ideal (M.geoTransform C π).E := by
  let Q := nextTotalMarked M.N M.ideal C π
  let A := idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  have hcQ : Q.ideal.IsCoherent := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    (⟨M.N,[],M.ideal,0⟩ : MarkedIdeal n X) hw.isClosedSubmanifold_N hw.isCoherent hπ hC.subset_N
  have hnzQ : ∀ y ∈ Q.N,IsNonzeroAlongAt Q.N Q.ideal y :=
    HironakaCoherentTransformExtension.isNonzeroAlongAt_geoTransform_without_admissibility
      (⟨M.N,[],M.ideal,0⟩ : MarkedIdeal n X) hw.isClosedSubmanifold_N hw.isCoherent hπ hC.subset_N hnz
  obtain ⟨hcA,hnzA,hmA⟩ := actual_new_exceptional_power_monomial hn hw.isClosedSubmanifold_N hw.isSNCDivisor
    hw.isTransverse hπ hC.subset_N hC.2.2 M.d
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hDivRaw : RestrictLe Q.N (GermIdeal.pullback (m := n) π M.ideal) A := by
    have hOld := HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport hw.isCoherent hw.isClosedSubmanifold_N
      hC.1 hC.subset_N hC.2.1
    have hPull := RestrictLeCalculus.restrictLe_pullback hπ.contMDiff (W := Q.N)
      (fun y hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hw.isClosedSubmanifold_N.1 hy)
      (GermIdealPullbackCalculus.isCoherent_idealPow hIC _) hOld
    rwa [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hIC] at hPull
  have hTot := geoTransform_zeroMark_ideal_eq_restricted_total (⟨M.N,[],M.ideal,0⟩ : MarkedIdeal n X) rfl C π
  change Q.ideal=restrictOn n Q.N (GermIdeal.pullback (m := n) π M.ideal) at hTot
  have hDiv : RestrictLe Q.N Q.ideal A := by
    rw [hTot]
    exact RestrictLeCalculus.RestrictLe.trans restrictLe_restrictOn hDivRaw
  have hColon : colonAlong n Q.N Q.ideal A=(M.geoTransform C π).ideal := by
    rw [hTot]
    change colon (restrictOn n Q.N (restrictOn n Q.N (GermIdeal.pullback (m := n) π M.ideal))) A=
      colon (restrictOn n Q.N (GermIdeal.pullback (m := n) π M.ideal)) A
    rw [restrictOn_idempotent]
  have hEq := actual_monomial_division_nonmonomial_eq hn hwP.isClosedSubmanifold_N hwP.isSNCDivisor hwP.isTransverse
    hcQ hnzQ hcA hnzA hmA (isInvertibleAlong_geoStrictTransform hπ M.N M.d) hDiv
  change nonmonomialPartAlong n Q.N Q.ideal (M.geoTransform C π).E=
    nonmonomialPartAlong n Q.N (colonAlong n Q.N Q.ideal A) (M.geoTransform C π).E at hEq
  rw [hColon] at hEq
  exact hEq.symm

end
end Hironaka.HironakaSharpActualMonomialDivisionResidual
