/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualStrictTraceOpenNonmonomial

/-! Actual raw TOTAL whole open pullback and independent all-power STRICT
comparison for ANY real member blowup, with no centre-in-member hypothesis. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualRawMemberOpenStrict
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualStrictTraceOpenNonmonomial HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaSharpOriginalFirstMemberWholeFactor HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension MarkedIdealRestrictOpen BlowupRestrictOpen
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  InvertibleIdealQuotient GermIdealTotalTransform GermIdealOrder
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual restricted finite-span germs and genuine coherent pullback give
WHOLE normalization commutation, without an ideal-comparison premise. -/
theorem actual_restrictOn_whole_open_pullback {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (U : Opens X) :
    restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)=
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (restrictOn n N I) := by
  have hcR := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  ext x g
  exact (restrictOn_pullback_val_iff U hI).trans (mem_pullback_val_iff U hcR).symm

/-- The SAME restricted projection and literal strict-carrier restriction
supply the WHOLE raw TOTAL open pullback before residuals are compared. -/
theorem actual_raw_total_whole_open_pullback {N C : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (U : Opens X) :
    let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V → U := fun z => ⟨π z,z.property⟩
    let CU := (Subtype.val : U → X) ⁻¹' C
    let NU := (Subtype.val : U → X) ⁻¹' N
    restrictOn n (BlowupStrictSubmanifold.geoStrictTransform ρ CU NU)
      (GermIdeal.pullback (m := n) ρ (GermIdeal.pullback (m := n) (Subtype.val : U → X) I))=
      GermIdeal.pullback (m := n) (Subtype.val : V → Y)
        (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I)) := by
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun z => ⟨π z,z.property⟩
  have hρ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (hπ.contMDiff.comp contMDiff_subtype_val)
  have hRaw : GermIdeal.pullback (m := n) (Subtype.val : V → Y) (GermIdeal.pullback (m := n) π I)=
      GermIdeal.pullback (m := n) ρ (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) := by
    rw [←pullback_comp hπ.contMDiff contMDiff_subtype_val hI,
      ←pullback_comp contMDiff_subtype_val hρ hI]
    rfl
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hI' := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI
  have hStrict := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen N
  change restrictOn n (BlowupStrictSubmanifold.geoStrictTransform ρ _ _)
    (GermIdeal.pullback (m := n) ρ (GermIdeal.pullback (m := n) (Subtype.val : U → X) I))=_
  rw [hStrict,←hRaw]
  exact actual_restrictOn_whole_open_pullback hN' hI' V

/-- ONLY actual original member geometry produces raw residual = independent
ALL-power relative STRICT on ANY real blowup CsubsetN, including mixed incidence. -/
theorem actual_any_member_raw_nonmonomial_eq_relative_strict (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    nonmonomialPartAlong n N' (restrictOn n N'
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))) [π ⁻¹' C]=
      firstRelativeStrictMemberIdeal N H C π := by
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  let P := memberTotalMarked N H C π
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x :=
    fun _ hx => HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hw0 : M0.IsWellFormed := ⟨hN,hcH,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hhol : ∀ x g,(vanishingIdeal (n := n) H).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hC0 : M0.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (vanishingIdeal (n := n) H) 0
    rw [cosupport_zero hhol]
    exact hCN
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw0 hC0 hπ
  have hnzP := isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hcH hπ hCN hnzH
  have hTotal : P.ideal=restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) :=
    geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  have hprP := fun y (_hy : y ∈ P.N) =>
    exists_actual_original_member_total_principal (W := N) hn hH hπ (0 : Fin [H].length) y
  obtain ⟨hSat,_hcSat,_hnzSat⟩ := actual_single_exceptional_saturation_eq_residual hn
    hwP.isClosedSubmanifold_N hwP.isSNCDivisor hwP.isTransverse hwP.isCoherent hnzP hprP
  have hIndependent : relativeExceptionalSaturation N' P.ideal (π ⁻¹' C)=firstRelativeStrictMemberIdeal N H C π := by
    ext y g
    rw [hTotal]
    exact relativeExceptionalSaturation_restrictOn_mem_iff _ _ _ y g
  change relativeExceptionalSaturation N' P.ideal (π ⁻¹' C)=
    nonmonomialPartAlong n N' P.ideal [π ⁻¹' C] at hSat
  rw [hIndependent,hTotal] at hSat
  exact hSat.symm

end
end Hironaka.HironakaSharpActualRawMemberOpenStrict
