/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveLocalSharpEndpoints

/-! Actual FIRST-Z order-two cuts and literal exceptional-difference naturality.
Every restricted TEST and ordered boundary comes from the original record.
No recipe comparison, padding, cocycle or global sharp scheduler is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveDefectRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveFirstDefectErasure HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualOriginalControlledHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalDeepProductBlowup
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen BlowupTowerTransforms HomogenizedGlueingTower NonmonomialOrderLocal
  IdealWeightPowers HironakaCoherentTransformExtension BlowupRestrictOpen NormalCrossingsInvariance
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Both true proper-position/quotient-class count directions precede the
whole actual chronological product's second-order cosupport identity. -/
theorem original_curve_first_defect_eq_product_cosupport_two (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    chronologicalDistinctDefect W E T=
      cosupport n (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) 2 := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template _ hwM T hT
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hGeom).isClosedSubmanifold_N
  obtain ⟨hcP,hnzP,_hprP,_hsum⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hGeom
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hfam : ∀ i : Fin E.length,(F i).IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T).N (F i) y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧
          IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N (·=f) y a := by
    intro i
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hGeom
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  ext x
  by_cases hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N
  · rw [ordinaryTraceOrder_cosupport_iff hN hcP hnzP hx 2]
    have hiff : x ∉ chronologicalDistinctDefect W E T ↔
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x≤1 := by
      refine ⟨original_curve_first_good_order_le_one hn hW hE hdense hr T hGeom hx,?_⟩
      intro hle
      rw [chronological_product_eq_actual_family_product W E T] at hle
      exact (actual_product_order_le_one_count_dictionary hN (fun i => (hfam i).1)
        (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hx hle).2.2
    constructor
    · intro hz
      by_contra hlt
      have hle : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x≤1 := by omega
      exact (hiff.mpr hle) hz
    · intro hge
      by_contra hz
      have hle := hiff.mp hz
      omega
  · exact ⟨fun hz => (hx hz.1).elim,fun hz => (hx hz.1).elim⟩

/-- WHOLE independently proved original controlled residual equality gives
the exact second cut for the SAME original record, not a rebased current input. -/
theorem original_curve_first_defect_eq_ordGe_two (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    chronologicalDistinctDefect W E T=ordGe (geoTransformAlong (originalMemberProductMarked W E 1) T) 2 := by
  rw [original_curve_first_defect_eq_product_cosupport_two hn hW hE hdense hr T hT]
  have hResidual := (original_product_controlled_history_residual_dictionary hn hW hE hdense 1 T hT).1
  change _=cosupport n _ (MonomialPartAlong.nonmonomialPartAlong n _ _ _) 2
  rw [hResidual,geoTransformAlong_N_eq_of_N_eq (𝔍 := originalMemberProductMarked W E 1)
    (𝔪 := geometricTemplate W []) rfl T]

private theorem original_curve_open_inputs {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (U : Opens X) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    IsClosedSubmanifold n WU ∧ IsSNCDivisor n EU ∧
      WU ⊆ closure (WU \ ⋃ H ∈ EU,H) ∧ ∀ x ∈ WU,RegularAtDim (n := n) WU x 1 := by
  refine ⟨isClosedSubmanifold_preimage_val hW U,
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE,?_,
    fun x hx => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr x.val hx)⟩
  intro y hy
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
  erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
    continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

/-- Genuine original open pullback/TEST restriction and second-cut transport
construct BOTH FIRST-Z restriction directions, retaining every empty position. -/
theorem original_curve_first_defect_restrict (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) (U : Opens X) :
    chronologicalDistinctDefect ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)=
        (Subtype.val : openPreimage T U → Y) ⁻¹' chronologicalDistinctDefect W E T := by
  let M := originalMemberProductMarked W E 1
  have hM : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  obtain ⟨hWU,hEU,hdU,hrU⟩ := original_curve_open_inputs hW hE hdense hr U
  have hWhole := pullback_val_originalMemberProductMarked hn W hE 1 U
  have hTU := isGeoTestTower_restrict U hW hM.isWellFormed.isCoherent T hT
  rw [hWhole] at hTU
  rw [original_curve_first_defect_eq_ordGe_two hn hWU hEU hdU hrU (restrict U T) hTU,
    ←hWhole,geoTransformAlong_restrict U hW hM.isWellFormed.isCoherent T hT,
    original_curve_first_defect_eq_ordGe_two hn hW hE hdense hr T hT]
  have hQ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  ext z
  exact mem_ordGe_pullback_val_iff hn hQ.isWellFormed hQ.isNonzeroAlongAt (openPreimage T U) 2 z

private theorem indexed_union_eq_list_union {α β : Type*} (L : List α) (S : α → Set β) :
    (⋃ i : Fin L.length,S (L.get i))=⋃ a ∈ L,S a := by
  ext x
  constructor
  · rintro ⟨A,⟨i,rfl⟩,hx⟩
    exact mem_iUnion₂.mpr ⟨L.get i,List.get_mem L i,hx⟩
  · intro hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact mem_iUnion.mpr ⟨i,hxa⟩

/-- Literal ORIGINAL-position ideal-germ difference, transported via the true
ordered exceptional/strict-member formula, independently of FIRST Z or order. -/
theorem original_curve_actual_difference_restrict (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) (U : Opens X) :
    actualAmbientExceptionalDifference ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)=
        (Subtype.val : openPreimage T U → Y) ⁻¹' actualAmbientExceptionalDifference W E T := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  obtain ⟨hWU,hEU,hdU,hrU⟩ := original_curve_open_inputs hW hE hdense hr U
  have hTU := isGeoTestTower_restrict U hW hwM.isCoherent T hT
  rw [pullback_val_originalMemberProductMarked hn W hE 1 U] at hTU
  rw [original_curve_actual_exceptional_difference_eq hn hWU hEU hdU hrU (restrict U T) hTU,
    original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT]
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template _ hwM T hT
  have hTemp : MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate W [])=
      geometricTemplate (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) [] := by
    simp [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]
  have hRecord := geoTransformAlong_restrict U hW hw.isCoherent T hGeom
  rw [hTemp] at hRecord
  have hN := congrArg MarkedIdeal.N hRecord
  have hE' := congrArg MarkedIdeal.E hRecord
  rw [hN,hE',indexed_union_eq_list_union,indexed_union_eq_list_union]
  ext z
  simp only [MarkedIdeal.pullback,mem_inter_iff,mem_preimage,mem_iUnion,List.mem_map]
  constructor
  · rintro ⟨⟨hzN,⟨_,⟨D,hD,rfl⟩,hzD⟩⟩,⟨_,⟨H,hH,rfl⟩,hzH⟩⟩
    refine ⟨⟨hzN,⟨D,hD,hzD⟩⟩,H,hH,?_⟩
    change z ∈ (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T H
    rw [←strictAlong_restrict U T H]
    exact hzH
  · rintro ⟨⟨hzN,⟨D,hD,hzD⟩⟩,⟨H,hH,hzH⟩⟩
    refine ⟨⟨hzN,⟨_,⟨D,hD,rfl⟩,hzD⟩⟩,_,⟨H,hH,rfl⟩,?_⟩
    rw [strictAlong_restrict U T H]
    exact hzH

end
end Hironaka.HironakaSharpActualCurveDefectRestriction
