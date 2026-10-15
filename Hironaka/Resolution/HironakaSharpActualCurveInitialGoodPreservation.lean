/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveTwoPhaseIsomorphism
import Hironaka.Resolution.HironakaSharpOriginalDeepProductBlowup

/-! Literal initial NC-good recognition BEFORE whole SAME-projection
preservation and actual full-family transverse curve endpoint. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveInitialGoodPreservation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveTwoPhaseIsomorphism HironakaSharpOriginalDeepProductBlowup
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpActualCurveFirstDefectErasure HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualOriginalDynamicStep
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpOriginalProductTraceOrder HironakaCoherentTransformExtension
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  GermIdealOrder DivisorExponentAlong NonmonomialOrderLocal HomogenizedGlueingTower BlowupFlatCoordinates MemberTraceIdealAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual curve rank and actual free SNC coordinates bound INDEXED incidence,
without substituting it for a distinct ideal-germ count. -/
theorem actual_transverse_curve_boundary_count_le_one (hn : 0<n)
    {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {x : X} (hr : RegularAtDim (n := n) N x 1) : BoundaryCount.boundaryCount E x≤1 := by
  obtain ⟨k,Φ,σ,_hsrc,hNflat,hfree,hinj,_hA,_hp,_hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE hT hr.2.1
  have hNk : RegularAtDim (n := n) N x (min k n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun {y} hy hyΦ => by
        have h := hNflat hy hyΦ
        rw [←BoundaryCount.complexCoordinatePlane_min] at h
        exact h) hr.2.1 (mem_chart_source _ x) Φ.center_mem_source
  have hk : min k n=1 := Nat.le_antisymm
    (RegularPointDimension.le_of_regularAtDim hNk hr) (RegularPointDimension.le_of_regularAtDim hr hNk)
  unfold BoundaryCount.boundaryCount
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hxi := (Finset.mem_filter.mp hi).2
  have hxj := (Finset.mem_filter.mp hj).2
  have hsi : (σ i).val < min k n := Nat.lt_min.mpr ⟨hfree i hxi,(σ i).isLt⟩
  have hsj : (σ j).val < min k n := Nat.lt_min.mpr ⟨hfree j hxj,(σ j).isLt⟩
  rw [hk] at hsi hsj
  exact hinj hxi hxj (Fin.ext (by omega))

/-- Genuine local NC coordinates and whole product open pullback first prove
actual ORIGINAL product order at most one. -/
theorem original_curve_initial_nc_product_order_le_one (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {x : X} (hx : x ∈ W) (hr : RegularAtDim (n := n) W x 1)
    (hNC : normalCrossingsAt (n := n) W E x) :
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x≤1 := by
  obtain ⟨U,hxU,hEU,hTU,hord⟩ := exists_actual_original_product_order_neighborhood hn hW.1 hE hdense hNC
  let z : U := ⟨x,hxU⟩
  have hrU : RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' W) z 1 :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hr
  have hcount := actual_transverse_curve_boundary_count_le_one (X := CMfd.of (n := n) U) hn hEU hTU hrU
  have hnot : x ∉ (originalMemberProductMarked W E 2).cosupp := by
    intro hx2
    have hz2 : z ∈ (originalMemberProductMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 2).cosupp := by
      rw [←pullback_val_originalMemberProductMarked hn W hE 2 U,
        MarkedIdealRestrictOpen.cosupp_pullback_val]
      · exact hx2
      · exact fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_originalMemberProduct hn hE) hg
    have hh := (hord z hx 2).mp hz2
    rw [distinctProperTraceGermCount_eq_boundaryCount hn hEU hTU hx] at hh
    omega
  have hNo : ¬2≤ordinaryTraceOrder W (originalMemberProduct (n := n) E) x := by
    intro hh
    exact hnot ((ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE)
      (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) hx 2).mpr hh)
  omega

/-- ONLY genuine original geometry recognizes the ENTIRE literal initial good
set inside actual FIRST-Z complement, with real proper/quotient counts first. -/
theorem original_curve_initial_good_subset_first_defect_complement (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) :
    originalGoodLocus (n := n) W E ⊆ (chronologicalDistinctDefect W E (.refl : BlowupTower X X))ᶜ := by
  intro x hxGood hz
  have hx : x ∈ W := hz.1
  have hxNC : normalCrossingsAt (n := n) W E x := by
    rcases hxGood with hxout | hxnc
    · exact False.elim (hxout hx)
    · exact hxnc.2
  have hOld := original_curve_initial_nc_product_order_le_one hn hW hE hdense hx (hr x hx) hxNC
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i))
    (.refl : BlowupTower X X)).ideal
  have hfam (i : Fin E.length) := original_members_actual_finite_chronological_geometry
    hn hW hE hdense i (.refl : BlowupTower X X) trivial
  have he := (original_product_nmOrd_eq_current hn hW hE hdense 1 (.refl : BlowupTower X X) trivial x).trans
    (HironakaSharpActualDynamicDistinctCentre.currentProductMarked_nmOrd_eq_ordinaryTraceOrder
      hn hW hE hdense (.refl : BlowupTower X X) trivial x)
  have hLE : ordinaryTraceOrder W (relativeIdealListProduct W (List.ofFn F)) x≤1 := by
    have hp := chronological_product_eq_actual_family_product W E (.refl : BlowupTower X X)
    change chronologicalMemberProduct W E (.refl : BlowupTower X X)=relativeIdealListProduct W (List.ofFn F) at hp
    rw [←hp]
    exact he ▸ hOld
  exact (actual_product_order_le_one_count_dictionary hW (fun i => (hfam i).2.2.2.1.isCoherent)
    (fun i => (hfam i).2.2.2.2.1) (fun i => (hfam i).2.2.2.2.2) hx hLE).2.2 hz

/-- Original compact true cosupport internally constructs the SAME proper
history and full endpoint geometry BEFORE whole initial-good preservation. -/
theorem exists_original_curve_whole_good_preserving_transverse_endpoint (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (hK : IsCompact (originalMemberProductMarked W E 1).cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧
      chronologicalDistinctDefect W E T=∅ ∧
      HironakaSharpActualCurveExceptionalDifference.actualAmbientExceptionalDifference W E T=∅ ∧
      IsProperMap T.proj ∧ IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1) T) ∧
      IsSNCDivisor n (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) ∧
      IsTransverse n (geoTransformAlong (geometricTemplate W []) T).N
        (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) ∧
      IsIsomorphismOver n T.proj (originalGoodLocus (n := n) W E) := by
  obtain ⟨Y,T,hTest,hZ,hD,hProper,hDom,hSNC,hTrans,hIso⟩ :=
    exists_original_curve_two_phase_transverse_isomorphism hn hW hE hdense hr hK
  have hsub := original_curve_initial_good_subset_first_defect_complement hn hW hE hdense hr
  refine ⟨Y,T,hTest,hZ,hD,hProper,hDom,hSNC,hTrans,⟨⟨fun y hy => hy,?_,?_⟩,?_⟩⟩
  · intro y hy y' hy' heq
    exact hIso.1.2.1 (hsub hy) (hsub hy') heq
  · intro x hx
    obtain ⟨y,hy,heq⟩ := hIso.1.2.2 (hsub hx)
    exact ⟨y,by change T.proj y ∈ originalGoodLocus (n := n) W E;rw [heq];exact hx,heq⟩
  · exact disjoint_left.mpr fun y hy hexc => disjoint_left.mp hIso.2 (hsub hy) hexc

end
end Hironaka.HironakaSharpActualCurveInitialGoodPreservation
