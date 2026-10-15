/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveInitialGoodPreservation
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-! Genuine local sharp curve endpoints at EVERY original ambient point.
Actual zero-dimensional cosupport supplies the compact open presentation;
no caller compactness/window/history or terminal-geometry certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveLocalSharpEndpoints
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveInitialGoodPreservation HironakaSharpOriginalDeepProductBlowup
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualCurveExceptionalDifference
  HironakaOneDimensionalCanonicalSuperlevels CodimOneSupportAlong AnalyticDimensionBasics
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  NormalCrossings NormalCrossingsInvariance MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual analytic zero-dimensional cosupport, real isolated open, and BOTH
whole pulled-cosupport directions supply genuine local compactness internally. -/
theorem exists_actual_curve_compact_cosupport_open (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (x : X) :
    ∃ U : Opens X,x ∈ U ∧
      IsCompact (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp := by
  have hAnalytic := isComplexAnalyticSubset_cosupport_along hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N hM.one_le_d
  have hclosed : IsClosed M.cosupp := hAnalytic.isClosed
  have hHol : ∀ y g,M.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  by_cases hx : x ∈ M.cosupp
  · have hReg := regularAtDim_zero_of_analytic_dimLE_zero hAnalytic (dimLE_cosupport_of_isInvDomain hM) hx
    obtain ⟨V,hV,hxV,hsub⟩ :=
      PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hReg
    let U : Opens X := ⟨V,hV⟩
    let p : U := ⟨x,hxV⟩
    refine ⟨U,hxV,?_⟩
    rw [cosupp_pullback_val M hHol]
    apply (isCompact_singleton (x := p)).of_isClosed_subset (hclosed.preimage continuous_subtype_val)
    intro y hy
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    exact mem_singleton_iff.mp (hsub ⟨hy,y.property⟩)
  · let U : Opens X := ⟨M.cosuppᶜ,hclosed.isOpen_compl⟩
    refine ⟨U,hx,?_⟩
    rw [cosupp_pullback_val M hHol]
    have he : (Subtype.val : U → X) ⁻¹' M.cosupp=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact y.property hy
    rw [he]
    exact isCompact_empty

/-- ONLY original smooth-curve/SNC/density and ANY basepoint construct the
actual open, WHOLE original restricted record and genuine local sharp endpoint. -/
theorem exists_original_curve_actual_local_sharp_endpoint (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (x : X) :
    ∃ U : Opens X,x ∈ U ∧
      let WU := (Subtype.val : U → X) ⁻¹' W
      let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let M := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsGeoTestTower M T ∧ chronologicalDistinctDefect WU EU T=∅ ∧
        actualAmbientExceptionalDifference WU EU T=∅ ∧
        IsProperMap T.proj ∧ IsInvDomain 1 (geoTransformAlong M T) ∧
        IsSNCDivisor n (EU.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate WU []) T).E) ∧
        IsTransverse n (geoTransformAlong (geometricTemplate WU []) T).N
          (EU.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate WU []) T).E) ∧
        IsIsomorphismOver n T.proj (originalGoodLocus (n := n) WU EU) := by
  let M := originalMemberProductMarked W E 1
  have hM : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun y hy => ⟨1,le_rfl,hr y hy⟩,le_rfl,
      fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy⟩
  obtain ⟨U,hxU,hK⟩ := exists_actual_curve_compact_cosupport_open M hM x
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  have hWhole : MarkedIdeal.pullback (Subtype.val : U → X) M=
      originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1 :=
    pullback_val_originalMemberProductMarked hn W hE 1 U
  have hDom := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hWU : IsClosedSubmanifold n WU := hDom.isWellFormed.isClosedSubmanifold_N
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hrU : ∀ y ∈ WU,RegularAtDim (n := n) WU y 1 :=
    fun y hy => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr y.val hy)
  have hdenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU,H) := by
    intro y hy
    have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  have hKU : IsCompact (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1).cosupp := by
    rw [←hWhole]
    exact hK
  exact ⟨U,hxU,exists_original_curve_whole_good_preserving_transverse_endpoint
    (X := CMfd.of (n := n) U) hn hWU hEU hdenseU hrU hKU⟩

end
end Hironaka.HironakaSharpActualCurveLocalSharpEndpoints
