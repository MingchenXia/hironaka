/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalFirstBlowupOpenComparison
import Hironaka.Resolution.HironakaSharpActualFiniteChronologicalHistory
import Hironaka.Resolution.HironakaOriginalCoherentHistoryYearOpenNaturality
/-! True arbitrary-power exceptional saturation commutes with actual opens.
The genuine next chronological geometry supplies all structural coherence. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualRelativeSaturationOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpOriginalFirstBlowupOpenComparison HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaOriginalCoherentHistoryYearOpenNaturality HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealPullbackCalculus IdealWeightPowers
  GermIdealOrder DivisorExponentAlong NormalCrossings
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- EACH genuine coherent finite-power colon gives the entire all-power open equality. -/
theorem relativeExceptionalSaturation_open {N D : Set X} {I : GermIdeal n X}
    (hN : (vanishingIdeal (n := n) N).IsCoherent)
    (hD : (vanishingIdeal (n := n) D).IsCoherent) (hI : I.IsCoherent)
    (hS : (relativeExceptionalSaturation N I D).IsCoherent) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (relativeExceptionalSaturation N I D)=
      relativeExceptionalSaturation (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
        ((Subtype.val : U → X) ⁻¹' D) := by
  ext x g
  rw [mem_pullback_val_iff U hS]
  change (∃ k,(colonAlong n N I (idealPow (vanishingIdeal (n := n) D) k)).mem x.val
      (extendOpens U g)) ↔
    ∃ k,(colonAlong n ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
      (idealPow (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' D)) k)).mem x g
  apply exists_congr
  intro k
  have hPow := isCoherent_idealPow hD k
  have hColon := isCoherent_colonAlong_without_inclusion hI hN hPow
  have hk := colonAlong_pullback_val U hI hPow hColon
  rw [BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val hD,
    SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hk
  rw [hk,mem_pullback_val_iff U hColon]

/-- Actual ordinary geometry internally supplies saturation coherence before open comparison. -/
theorem nextRelativeStrict_open (hn : 0<n) {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x∈N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x∈N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C⊆N) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : firstBlowupSourceOpen hπ U → Y)
      (nextRelativeStrict N I C π)=
      nextRelativeStrict (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
        ((Subtype.val : U → X) ⁻¹' C) (firstBlowupOpenProjection hπ U) := by
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  let P := nextTotalMarked N I C π
  have hw : M.IsWellFormed := ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hadm : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C⊆cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hadm hπ
  have hS := (nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN).2.1
  have hD : (vanishingIdeal (n := n) (π ⁻¹' C)).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn (show IsSNCDivisor n [π ⁻¹' C] from hwP.isSNCDivisor) 0)
  have hRaw := isCoherent_pullback hπ.contMDiff hI
  have hPull := relativeExceptionalSaturation_open
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hwP.isClosedSubmanifold_N)
      hD hRaw hS (firstBlowupSourceOpen hπ U)
  have hCarrier := geoStrictTransform_restrict (C := C) (π := π) U (firstBlowupSourceOpen hπ U).isOpen N
  have hRawEq := actual_restricted_blowup_ideal_pullback hπ U hI
  change GermIdeal.pullback (m := n) (Subtype.val : firstBlowupSourceOpen hπ U → Y)
      (GermIdeal.pullback (m := n) π I)=
    GermIdeal.pullback (m := n) (firstBlowupOpenProjection hπ U)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) at hRawEq
  change GermIdeal.pullback (m := n) (Subtype.val : firstBlowupSourceOpen hπ U → Y)
      (nextRelativeStrict N I C π)=
    relativeExceptionalSaturation (X := CMfd.of (n := n) (firstBlowupSourceOpen hπ U))
      ((Subtype.val : firstBlowupSourceOpen hπ U → Y) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : firstBlowupSourceOpen hπ U → Y)
        (GermIdeal.pullback (m := n) π I))
      ((Subtype.val : firstBlowupSourceOpen hπ U → Y) ⁻¹' (π ⁻¹' C)) at hPull
  change BlowupStrictSubmanifold.geoStrictTransform (firstBlowupOpenProjection hπ U)
      ((Subtype.val : U → X) ⁻¹' C) ((Subtype.val : U → X) ⁻¹' N)=
      (Subtype.val : firstBlowupSourceOpen hπ U → Y) ⁻¹' P.N at hCarrier
  rw [←hCarrier,hRawEq] at hPull
  exact hPull

/-- ANY genuine original finite geometry supplies ALL actual old member inputs internally. -/
theorem original_member_next_strict_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) {C : Set Y} {Z : CMfd.{u} n} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (geometricTemplate W []) (.step T C π hπ))
    (U : Opens Y) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    GermIdeal.pullback (m := n) (Subtype.val : firstBlowupSourceOpen hπ U → Z)
      (nextRelativeStrict A.N A.ideal C π)=
      nextRelativeStrict (X := CMfd.of (n := n) U)
        ((Subtype.val : U → Y) ⁻¹' A.N) (GermIdeal.pullback (m := n) (Subtype.val : U → Y) A.ideal)
        ((Subtype.val : U → Y) ⁻¹' C) (firstBlowupOpenProjection hπ U) := by
  dsimp only
  obtain ⟨hAN,_hAE,_hm,hwA,hnzA,hprA⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT.1
  have hCN : C⊆(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N := by
    rw [hAN]
    exact hT.2.subset_N
  exact nextRelativeStrict_open hn hwA.isClosedSubmanifold_N hwA.isCoherent hnzA hprA hπ hCN U
end
end Hironaka.HironakaSharpActualRelativeSaturationOpenNaturality
