/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveExceptionalResidualUnit
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-! The ENTIRE literal curve FIRST Z is a genuine SAME ORIGINAL-record
global centre, without compactness or canonicality. New-Z erasure remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveWholeDefectCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveExceptionalResidualUnit HironakaSharpActualFirstGoodLowerDimension
  HironakaSharpActualOriginalControlledHistory HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualDynamicDistinctCentre HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaCoherentTransformExtension
  HironakaOneDimensionalCanonicalSuperlevels RelativePrincipalizationSpan RestrictedIdealExtension
  DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  IdealWeightPowers MarkedIdealOperationsAlong ResolutionInvariantDriver ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual original curve geometry internally gives the tight current domain
and the WHOLE literal FIRST-Z positive-cosupport inclusion. -/
theorem actual_curve_product_domain_and_defect_cosupport (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    IsInvDomain 1 (currentProductMarked W E T) ∧
      chronologicalDistinctDefect W E T ⊆ (currentProductMarked W E T).cosupp := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  obtain ⟨hcP,hnzP,_hprP,_hOrdP⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hPure := actual_template_regular_dimension hW 1 hr T hT
  have hdom : IsInvDomain 1 (currentProductMarked W E T) :=
    ⟨⟨hwT.isClosedSubmanifold_N,hcP,hwT.isSNCDivisor,hwT.isTransverse⟩,
      fun y hy => ⟨1,le_rfl,hPure y hy⟩,le_rfl,hnzP⟩
  refine ⟨hdom,?_⟩
  intro x hx
  apply (ordinaryTraceOrder_cosupport_iff hwT.isClosedSubmanifold_N hcP hnzP hx.1 1).mpr
  have hpos := hx.2
  rw [←chronological_product_eq_actual_family_product W E T] at hpos
  change 1 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
    (chronologicalMemberProduct W E T) x
  omega

/-- The WHOLE independently computed FIRST Z is an actual SAME ORIGINAL
mark-one admissible centre; no compactness, canonicality or desired centre. -/
theorem original_curve_whole_defect_admissible (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre
      (chronologicalDistinctDefect W E T) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        RegularAtDim (n := n) (chronologicalDistinctDefect W E T) x 0) ∧
      Disjoint (chronologicalDistinctDefect W E T)
        (⋃ H ∈ (geoTransformAlong (geometricTemplate W []) T).E,H) := by
  let M := originalMemberProductMarked W E 1
  let Q := geoTransformAlong M T
  have hcI := isCoherent_originalMemberProduct hn hE
  have hwM : M.IsWellFormed := ⟨hW,hcI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hInit : IsInvDomain 1 M :=
    ⟨hwM,fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hGeom := actual_original_test_history_template M hwM T hT
  obtain ⟨_hPdom,hZP⟩ := actual_curve_product_domain_and_defect_cosupport hn hW hE hdense hr T hGeom
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hResidual := (original_product_controlled_history_residual_dictionary hn hW hE hdense 1 T hT).1
  obtain ⟨hcP,_hnzP,_hprP,_hOrdP⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hGeom
  have hLe : Q.ideal.Le (chronologicalMemberProduct W E T) := by
    rw [←hResidual]
    exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hDom.isWellFormed.isCoherent
  have hRestrict := RestrictLeCalculus.restrictLe_of_le (W := Q.N) hcP hLe
  have hZQ : chronologicalDistinctDefect W E T ⊆ Q.cosupp := by
    intro x hx
    have hxP := hZP hx
    change x ∈ cosupport n (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) 1 at hxP
    have hxQ : x ∈ cosupport n Q.N (chronologicalMemberProduct W E T) 1 := by rw [hQN];exact hxP
    change x ∈ cosupport n Q.N Q.ideal (geoTransformAlong M T).d
    rw [d_geoTransformAlong]
    exact cosupport_subset_of_restrictLe hRestrict 1 hxQ
  have hAdm := isAdmissibleCentre_subset_cosupport_of_isInvDomain_one hDom _ hZQ
  have hZA := isComplexAnalyticSubset_subset_cosupport_of_isInvDomain_one hDom _ hZQ
  have hQA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
    hDom.isWellFormed.isCoherent hDom.isWellFormed.isClosedSubmanifold_N hDom.one_le_d
  have hDimQ := dimLE_cosupport_of_isInvDomain hDom
  have hDimZ := DimensionMonotone.DimLE.anti hQA hZQ hDimQ
  refine ⟨hAdm,fun x hx => regularAtDim_zero_of_analytic_dimLE_zero hZA hDimZ hx,?_⟩
  apply Set.disjoint_left.mpr
  intro x hxZ hxE
  exact (original_curve_exceptional_residual_units_and_defect_disjoint hn hW hE hdense hr T hGeom x hxZ.1 hxE).2.2 hxZ

/-- Blow up EXACTLY the entire literal FIRST defect on the SAME original
record. Actual original domain/ordered SNC and the whole complement iso follow. -/
theorem exists_original_curve_whole_defect_blowup (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y)
      (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E T) π),
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      IsGeoTestTower (originalMemberProductMarked W E 1)
        (.step T (chronologicalDistinctDefect W E T) π hπ) ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1)
        (.step T (chronologicalDistinctDefect W E T) π hπ)) ∧
      IsSNCDivisor n ((geoTransformAlong (originalMemberProductMarked W E 1) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π (chronologicalDistinctDefect W E T)) ++
          [π ⁻¹' chronologicalDistinctDefect W E T]) := by
  let M := originalMemberProductMarked W E 1
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hC := (original_curve_whole_defect_admissible hn hW hE hdense hr T hT).1
  have hint : interior (chronologicalDistinctDefect W E T)=∅ :=
    eq_empty_of_subset_empty ((interior_mono hC.2.1).trans (interior_cosupp_eq_empty hDom).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup _ hC.1 hint
  have htNew : IsGeoTestTower M (.step T (chronologicalDistinctDefect W E T) π hπ) := ⟨hT,hC⟩
  have hNew := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit _ htNew
  exact ⟨Z,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,
    BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ,htNew,hNew,hNew.isWellFormed.isSNCDivisor⟩

end
end Hironaka.HironakaSharpActualCurveWholeDefectCentre
