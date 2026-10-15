/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveFullAmbientBoundary

/-! Actual ambient strict trace versus genuine chronological residual.
The true exceptional factor is retained; no support equality or tauD erasure. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstAmbientStrictTraceFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualControlledRelativeSaturation HironakaSharpActualMonomialDivisionResidual
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalFirstMemberExceptionalFactor
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient RestrictedIdealWeight
  RestrictLeCalculus MarkedIdealOperationsAlong InvertibleIdealQuotient MonomialPartAlong
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers DivisorExponentAlong GermIdealOrder
  HironakaCoherentTransformExtension
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual product/colon inclusions and genuine nonzero-along cancellation
construct the WHOLE quotient, retaining actual carrier normal germs. -/
theorem actual_relative_invertible_product_colon {N : Set X} (hN : IsClosedSubmanifold n N)
    {A B : GermIdeal n X} (hA : A.IsCoherent) (hB : B.IsCoherent)
    (hinv : IsInvertibleAlong n N A) : colonAlong n N (A.mul B) A=restrictOn n N B := by
  let I := A.mul B
  let J := colonAlong n N I A
  have hcI : I.IsCoherent := isCoherent_mul hA hB
  have hcN := VanishingIdealCoherent.isCoherent_vanishingIdeal hN
  have hLe : I.Le A := by
    intro x g hg
    change IsInSpanAt (n := n) (fun s => ∃ a b,A.mem x a ∧ B.mem x b ∧ s=a*b) x g at hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hA
    refine IsInSpanAt.trans ?_ hg
    rintro s ⟨a,b,ha,hb,rfl⟩
    have hah := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA ha
    have hbh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB hb
    exact isInSpanAt_of_eq_mul ha (hah.mul hbh) hbh (Eventually.of_forall fun _ => mul_comm _ _)
  have hDiv := restrictLe_of_le (W := N) hA hLe
  have hcJ : J.IsCoherent := isCoherent_colonAlong hN.1 hcI hcN hA hinv hDiv
  have hProd : RestrictLe N (J.mul A) (B.mul A) := by
    rw [mul_comm' J A,mul_comm' B A]
    exact restrictLe_mul_colon' hcI hcN
  have hJB : RestrictLe N J B := restrictLe_of_restrictLe_mul_mul hcJ hB hinv hProd
  have hBLeJ : B.Le J := by
    intro x g hg
    have hgh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB hg
    refine ⟨hgh,fun a ha => ?_⟩
    have hah := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA ha
    have hprod : I.mem x (a*g) := by
      change IsInSpanAt (n := n) (fun s => ∃ a b,A.mem x a ∧ B.mem x b ∧ s=a*b) x (a*g)
      exact isInSpanAt_self ⟨a,g,ha,hg,rfl⟩ (hah.mul hgh)
    exact le_restrictOn hcI x (a*g) hprod
  have hBJ := restrictLe_of_le (W := N) hcJ hBLeJ
  have hRes := restrictOn_eq_of_restrictLe hN.1 hJB hBJ
  have hNorm : restrictOn n N J=J := by
    ext x g
    exact restrictOn_colonAlong_mem_iff N I A
      (fun a ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA ha) g
  exact hNorm.symm.trans hRes

/-- Genuine ambient pullback product and actual relative cancellation supply
the TRUE ambient strict-member trace as a WHOLE original controlled ideal. -/
theorem actual_first_controlled_ambient_strict_trace {N H C : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H) :
    ((⟨N,[],vanishingIdeal (n := n) H,1⟩ : MarkedIdeal n X).geoTransform C π).ideal=
      restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)) := by
  let A := (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal
  have hNc := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hHc := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hH hCH
  have hcA : A.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)
  have hPow : idealPow A 1=A := BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ
  have hinv := isInvertibleAlong_geoStrictTransform hπ N 1
  change IsInvertibleAlong n (BlowupStrictSubmanifold.geoStrictTransform π C N) (idealPow A 1) at hinv
  rw [hPow] at hinv
  change colonAlong n (BlowupStrictSubmanifold.geoStrictTransform π C N)
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) (idealPow A 1)=_
  rw [hPow,BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hπ hH hCH]
  exact actual_relative_invertible_product_colon hNc hcA
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hHc) hinv

/-- The actual ambient strict trace has its independently computed greatest
exceptional factor times the independently defined true all-power STRICT.
The WHOLE factorization retains the essential OUTER carrier restriction. -/
theorem actual_first_ambient_strict_trace_factor_dictionary (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let E' := [π ⁻¹' C]
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let J' := firstRelativeStrictMemberIdeal N H C π
    let D' := monomialPartAlong n N' I' E'
    I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      D'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' D' y) ∧ IsMonomialAlong n N' D' E' ∧
      nonmonomialPartAlong n N' I' E'=J' ∧ I'=restrictOn n N' (D'.mul J') := by
  let M : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,1⟩
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  let Q := M.geoTransform C π
  let P := memberTotalMarked N H C π
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  let S := firstRelativeStrictMemberIdeal N H C π
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hwM : M.IsWellFormed := ⟨hN,hcH,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hw0 : M0.IsWellFormed := ⟨hN,hcH,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hnz : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x :=
    fun _ hx => HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hhol : ∀ x g,(vanishingIdeal (n := n) H).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hC : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (vanishingIdeal (n := n) H) 1
    rw [cosupport_one hhol]
    intro x hx
    exact ⟨hCN hx,fun g hg => hg.2.self_of_nhds (hCH hx)⟩
  have hC0 : M0.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (vanishingIdeal (n := n) H) 0
    rw [cosupport_zero hhol]
    exact hCN
  have hwQ := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwM hC hπ
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw0 hC0 hπ
  have hnzQ := isNonzeroAlongAt_geoTransform_without_admissibility M hN hcH hπ hCN hnz
  have hnzP := isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hcH hπ hCN hnz
  have hTrace : Q.ideal=I' := actual_first_controlled_ambient_strict_trace hN hHsm hπ hCN hCH
  have hTotal : P.ideal=restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) :=
    geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  have hprP := fun y (_hy : y ∈ P.N) =>
    exists_actual_original_member_total_principal (W := N) hn hH hπ (0 : Fin [H].length) y
  obtain ⟨hSat,_hcSat,_hnzSat⟩ := HironakaSharpOriginalFirstMemberWholeFactor.actual_single_exceptional_saturation_eq_residual hn
    hwP.isClosedSubmanifold_N hwP.isSNCDivisor hwP.isTransverse hwP.isCoherent hnzP hprP
  have hSatS : relativeExceptionalSaturation N' P.ideal (π ⁻¹' C)=S := by
    ext y g
    rw [hTotal]
    exact relativeExceptionalSaturation_restrictOn_mem_iff _ _ _ y g
  change relativeExceptionalSaturation N' P.ideal (π ⁻¹' C)=
    nonmonomialPartAlong n N' P.ideal [π ⁻¹' C] at hSat
  rw [hSatS] at hSat
  have hControlled := actual_geoTransform_nonmonomial_eq_total hn M hwM hnz hC hπ
  change nonmonomialPartAlong n N' Q.ideal [π ⁻¹' C]=nonmonomialPartAlong n N' P.ideal [π ⁻¹' C] at hControlled
  rw [hTrace] at hControlled
  have hResidual : nonmonomialPartAlong n N' I' [π ⁻¹' C]=S := hControlled.trans hSat.symm
  have hwi : (⟨N',[π ⁻¹' C],I',1⟩ : MarkedIdeal n Y).IsWellFormed :=
    ⟨hwQ.isClosedSubmanifold_N,hTrace ▸ hwQ.isCoherent,hwQ.isSNCDivisor,hwQ.isTransverse⟩
  have hnzi : ∀ y ∈ N',IsNonzeroAlongAt N' I' y := by
    rw [←hTrace]
    exact hnzQ
  obtain ⟨_hcR,hcD,hnzD,hmD,_hNoFactor,_hnzR,hFactor⟩ :=
    NonmonomialTransformAlong.parts_hypotheses hn (⟨N',[π ⁻¹' C],I',1⟩ : MarkedIdeal n Y) hwi hnzi
  have hWhole := restrictOn_eq_of_restrictLe hwi.isClosedSubmanifold_N.1 hFactor.le hFactor.ge
  change restrictOn n N' I'=restrictOn n N' ((nonmonomialPartAlong n N' I' [π ⁻¹' C]).mul
    (monomialPartAlong n N' I' [π ⁻¹' C])) at hWhole
  rw [hResidual,mul_comm' S (monomialPartAlong n N' I' [π ⁻¹' C])] at hWhole
  have hNorm : restrictOn n N' I'=I' := by
    ext y g
    constructor
    · rintro ⟨hg,hspan⟩
      exact ⟨hg,IsInSpanOnAt.trans (fun a ha => ha.2) hspan⟩
    · intro hg
      exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩
  exact ⟨hwi.isCoherent,hnzi,hcD,hnzD,hmD,hResidual,hNorm.symm.trans hWhole⟩

end
end Hironaka.HironakaSharpActualFirstAmbientStrictTraceFactor
