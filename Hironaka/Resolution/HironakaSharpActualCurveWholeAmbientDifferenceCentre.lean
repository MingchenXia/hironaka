/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveContactBudgetDomination

/-! The ENTIRE literal actual ambient I/J difference is a genuine SAME
original positive-record centre. FIRST Z and sharp Sigma remain distinct. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveWholeAmbientDifferenceCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveContactBudgetDomination HironakaSharpActualCurveOffCentreOrders
  HironakaSharpActualCurveControlledOrderShift HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualCurveAmbientContactBudget HironakaSharpActualChronologicalAmbientTrace
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualOriginalControlledHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain HironakaCoherentTransformExtension
  HironakaOneDimensionalCanonicalSuperlevels RelativePrincipalizationSpan NormalCrossings NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower IdealWeightPowers
  ResolutionInvariantDriver ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The independently proved real original support inclusion supplies EVERY
original-admissibility field for the ENTIRE literal ambient difference. -/
theorem original_curve_whole_ambient_difference_admissible (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre
      (actualAmbientExceptionalDifference W E T) := by
  have hInit : IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  exact isAdmissibleCentre_subset_cosupport_of_isInvDomain_one hDom _
    (original_curve_actual_difference_subset_cosupport hn hW hE hdense hr T hT)

/-- ONLY original data construct the SAME global whole-difference blowup,
whole complement inverse, original TEST/domain/SNC, and genuine real drops. -/
theorem exists_original_curve_whole_ambient_difference_blowup (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n (actualAmbientExceptionalDifference W E T) π),
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (actualAmbientExceptionalDifference W E T)ᶜ ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) (.step T (actualAmbientExceptionalDifference W E T) π hπ) ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1) (.step T (actualAmbientExceptionalDifference W E T) π hπ)) ∧
      IsSNCDivisor n ((geoTransformAlong (originalMemberProductMarked W E 1) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π (actualAmbientExceptionalDifference W E T)) ++
          [π ⁻¹' actualAmbientExceptionalDifference W E T]) ∧
      ∀ z ∈ (geoTransformAlong (originalMemberProductMarked W E 1) (.step T (actualAmbientExceptionalDifference W E T) π hπ)).N,
        π z ∈ actualAmbientExceptionalDifference W E T →
          actualAmbientContactBudget W E (.step T (actualAmbientExceptionalDifference W E T) π hπ) z<
            actualAmbientContactBudget W E T (π z) ∧
          ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) (.step T (actualAmbientExceptionalDifference W E T) π hπ)).N
            (geoTransformAlong (originalMemberProductMarked W E 1) (.step T (actualAmbientExceptionalDifference W E T) π hπ)).ideal z+1=
          ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) T).N
            (geoTransformAlong (originalMemberProductMarked W E 1) T).ideal (π z) := by
  let M := originalMemberProductMarked W E 1
  let C := actualAmbientExceptionalDifference W E T
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hC := original_curve_whole_ambient_difference_admissible hn hW hE hdense hr T hT
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hC.2.1).trans (interior_cosupp_eq_empty hDom).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup C hC.1 hint
  have hNewT : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  have hNew := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit _ hNewT
  refine ⟨Z,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,
    BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ,hNewT,hNew,hNew.isWellFormed.isSNCDivisor,?_⟩
  intro z hz hzC
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl (.step T C π hπ)
  have hzA : z ∈ (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N := hQN ▸ hz
  exact ⟨original_curve_contact_budget_strict_drop_above_actual_difference hn hW hE hdense hr T hT hC hπ hzA hzC hzC,
    original_curve_product_next_controlled_order_drop hn hW hE hdense hr T hT hC hπ hz hzC⟩

/-- The actual full support dictionary and precise ordered strict-old-plus-NEW
boundary independently localize EVERY new actual difference above old Delta. -/
theorem original_curve_new_ambient_difference_over_old (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {π : Z → Y} (hπ : IsBlowupAlong n (actualAmbientExceptionalDifference W E T) π) :
    actualAmbientExceptionalDifference W E (.step T (actualAmbientExceptionalDifference W E T) π hπ) ⊆
      π ⁻¹' actualAmbientExceptionalDifference W E T := by
  let C := actualAmbientExceptionalDifference W E T
  let A := geoTransformAlong (geometricTemplate W []) T
  have hInit : IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template _ hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres _ hInit T hT
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hC := original_curve_whole_ambient_difference_admissible hn hW hE hdense hr T hT
  have hNewT : IsGeoTestTower (originalMemberProductMarked W E 1) (.step T C π hπ) := ⟨hT,hC⟩
  have hOldEq := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT
  have hNewEq := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr (.step T C π hπ) hNewT
  intro z hz
  have hzLit := hNewEq ▸ hz
  have hxN : π z ∈ A.N := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
    hπ.contMDiff.continuous hwA.isClosedSubmanifold_N.1 hzLit.1.1
  obtain ⟨i,hzi⟩ := mem_iUnion.mp hzLit.2
  have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
  have hDenseI : W ⊆ closure (W \ E.get i) := by
    apply Subset.trans hdense
    apply closure_mono
    exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
  have hHT := (actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc).1
  have hxi : π z ∈ strictAlong T (E.get i) := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
    hπ.contMDiff.continuous (hHT.1 _ (by simp)) hzi
  have hzF := hzLit.1.2
  change z ∈ ⋃ D ∈ A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C],D at hzF
  obtain ⟨D,hD,hzD⟩ := mem_iUnion₂.mp hzF
  rcases List.mem_append.mp hD with hOld | hNew
  · obtain ⟨D0,hD0,rfl⟩ := List.mem_map.mp hOld
    have hxD := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (hwA.isSNCDivisor.1 _ hD0) hzD
    change π z ∈ actualAmbientExceptionalDifference W E T
    rw [hOldEq]
    exact ⟨⟨hxN,mem_iUnion₂.mpr ⟨D0,hD0,hxD⟩⟩,mem_iUnion.mpr ⟨i,hxi⟩⟩
  · simp only [List.mem_singleton] at hNew
    subst D
    exact hzD

end
end Hironaka.HironakaSharpActualCurveWholeAmbientDifferenceCentre
