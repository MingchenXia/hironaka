/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveRetainedLocalRecipes

/-! Genuine base biholomorphisms construct original ordered curve data and
actual FIRST/difference stage centres before unique next blowup comparisons. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveBaseBiholomorphism
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveDefectRestriction HironakaSharpActualCurveStageComparison
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualOriginalControlledHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpSingleBoundaryTraceCentre IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  BlowupTowerIsomorphism NormalCrossings NormalCrossingsInvariance NormalCrossingsComparison
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong NonmonomialOrderLocal
  HomogenizedGlueingTower CodimOnePartCanonical
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

private theorem actual_biholo_vanishing_pullback
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (C : Set X) (hC : IsClosedSubmanifold n C) :
    GermIdeal.pullback (m := n) Φ (vanishingIdeal (n := n) C)=vanishingIdeal (n := n) (Φ ⁻¹' C) := by
  have hc := (isClosedSubmanifold_preimage_iff Φ).mpr hC
  have he := pullback_vanishingIdeal_preimage Φ.contMDiff Φ.symm.contMDiff
    Φ.apply_symm_apply Φ.symm_apply_apply (g := id) contMDiff_id C
  rw [Function.comp_id,BlowupControlledTransform.pullback_id
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hc)] at he
  exact he.symm

private theorem actual_biholo_product_pullback (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    GermIdeal.pullback (m := n) Φ (originalMemberProduct (n := n) E)=
      originalMemberProduct (n := n) (E.map (Φ ⁻¹' ·)) := by
  induction E with
  | nil => exact BlowupExceptionalDivisor.pullback_unitIdeal
  | cons H E ih =>
    have hTail := NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.sublist_cons_self H E)
    have hH : IsClosedSubmanifold n H := originalBoundary_isClosedSubmanifold hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.singleton_sublist.mpr (by simp)))
    change GermIdeal.pullback (m := n) Φ
      ((vanishingIdeal (n := n) H).mul (originalMemberProduct (n := n) E))=_
    rw [GermIdealTotalTransform.pullback_mul Φ.contMDiff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) (isCoherent_originalMemberProduct hn hTail),
      actual_biholo_vanishing_pullback Φ H hH,ih hTail]
    rfl

/-- ALL FOUR fields of the actual original source product, with each original
ordered member pulled through the SAME genuine base biholomorphism. -/
theorem pullback_biholo_originalMemberProductMarked (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (W : Set X) {E : List (Set X)} (hE : IsSNCDivisor n E) (q : ℕ) :
    MarkedIdeal.pullback Φ (originalMemberProductMarked W E q)=
      originalMemberProductMarked (X := X') (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) q := by
  simp [MarkedIdeal.pullback,originalMemberProductMarked,actual_biholo_product_pullback hn Φ hE]

/-- Genuine coordinate and closure transport internally give actual source
pure-curve/SNC/whole-family density; no source geometric certificate is input. -/
theorem original_curve_biholo_inputs
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) :
    IsClosedSubmanifold n (Φ ⁻¹' W) ∧ IsSNCDivisor n (E.map (Φ ⁻¹' ·)) ∧
      (Φ ⁻¹' W) ⊆ closure ((Φ ⁻¹' W) \ ⋃ H ∈ E.map (Φ ⁻¹' ·),H) ∧
      ∀ x ∈ Φ ⁻¹' W,RegularAtDim (n := n) (Φ ⁻¹' W) x 1 := by
  refine ⟨(isClosedSubmanifold_preimage_iff Φ).mpr hW,
    (isSNCDivisor_map_preimage_iff Φ).mpr hE,?_,
    fun x hx => (CodimOnePartCanonical.regularAtDim_preimage_iff Φ).mpr (hr (Φ x) hx)⟩
  intro x hx
  have hp : x ∈ Φ ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hx
  erw [Φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage Φ.continuous
    (W \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

/-- Original source TEST and whole current order transport are constructed
before BOTH genuine FIRST-Z directions over ANY actual base biholomorphism. -/
theorem original_curve_first_defect_biholo_isTowerIso (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    chronologicalDistinctDefect (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) T'=
      χ ⁻¹' chronologicalDistinctDefect W E T := by
  let M := originalMemberProductMarked W E 1
  have hM : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  obtain ⟨hW',hE',hd',hr'⟩ := original_curve_biholo_inputs Φ hW hE hdense hr
  have hWhole := pullback_biholo_originalMemberProductMarked hn Φ W hE 1
  have hT' := (IsTowerIso.isGeoTestTower_iff Φ hW hM.isWellFormed.isCoherent hiso).mpr hT
  rw [hWhole] at hT'
  rw [original_curve_first_defect_eq_ordGe_two hn hW' hE' hd' hr' T' hT',
    original_curve_first_defect_eq_ordGe_two hn hW hE hdense hr T hT]
  ext z
  have he := mem_ordGe_geoTransformAlong_isTowerIso hn Φ hM hiso hT 2 z
  rw [hWhole] at he
  exact he

private theorem actual_indexed_union_eq_list_union {α β : Type*} (L : List α) (S : α → Set β) :
    (⋃ i : Fin L.length,S (L.get i))=⋃ a ∈ L,S a := by
  ext x
  constructor
  · rintro ⟨A,⟨i,rfl⟩,hx⟩
    exact mem_iUnion₂.mpr ⟨L.get i,List.get_mem L i,hx⟩
  · intro hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact mem_iUnion.mpr ⟨i,hxa⟩

/-- The independent literal original-member ideal-germ difference is
transported through the WHOLE actual template and EACH original strict member. -/
theorem original_curve_difference_biholo_isTowerIso (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    actualAmbientExceptionalDifference (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) T'=
      χ ⁻¹' actualAmbientExceptionalDifference W E T := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  obtain ⟨hW',hE',hd',hr'⟩ := original_curve_biholo_inputs Φ hW hE hdense hr
  have hT' := (IsTowerIso.isGeoTestTower_iff Φ hW hwM.isCoherent hiso).mpr hT
  rw [pullback_biholo_originalMemberProductMarked hn Φ W hE 1] at hT'
  rw [original_curve_actual_exceptional_difference_eq hn hW' hE' hd' hr' T' hT',
    original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT]
  have hGeom := actual_original_test_history_template _ hwM T hT
  have hRecord := IsTowerIso.geoTransformAlong_eq Φ hW isCoherent_unitIdeal hiso hGeom
  have hTemp : MarkedIdeal.pullback Φ (geometricTemplate W [])=
      geometricTemplate (X := X') (Φ ⁻¹' W) [] := by
    simp [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]
  change geoTransformAlong (MarkedIdeal.pullback Φ (geometricTemplate W [])) T'=
    MarkedIdeal.pullback χ (geoTransformAlong (geometricTemplate W []) T) at hRecord
  rw [hTemp] at hRecord
  have hN := congrArg MarkedIdeal.N hRecord
  have hF := congrArg MarkedIdeal.E hRecord
  rw [hN,hF,actual_indexed_union_eq_list_union,actual_indexed_union_eq_list_union]
  have hStrict (H : Set X) : strictAlong T' (Φ ⁻¹' H)=χ ⁻¹' strictAlong T H := by
    simpa using hiso.strictAlong_eq H
  ext z
  simp [MarkedIdeal.pullback,hStrict]

/-- Compute the true FIRST centre preimage BEFORE constructing its genuine
next comparison and stagewise extension over the SAME actual base map. -/
theorem exists_original_curve_biholo_first_stage_comparison (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {π' : Z' → Y'} {π : Z → Y}
    (hπ' : IsBlowupAlong n (chronologicalDistinctDefect (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) T') π')
    (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E T) π) :
    ∃ e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso Φ (.step T' _ π' hπ') (.step T _ π hπ) e ∧
      (∀ z,π (e z)=χ (π' z)) ∧
      ∀ k : Z' → Z,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ k →
        (∀ z,π (k z)=χ (π' z)) → k=e := by
  have hC := (original_curve_first_defect_biholo_isTowerIso hn Φ hW hE hdense hr hiso hT).symm
  have hπ'' : IsBlowupAlong n (χ ⁻¹' chronologicalDistinctDefect W E T) π' := hC ▸ hπ'
  obtain ⟨e,hcomm,huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
  exact ⟨e,IsTowerIso.step hiso hπ' hπ e hcomm hC,hcomm,huniq⟩

/-- The same genuine construction uses the independent whole difference,
not a supplied equality or a replacement order/support locus. -/
theorem exists_original_curve_biholo_difference_stage_comparison (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {π' : Z' → Y'} {π : Z → Y}
    (hπ' : IsBlowupAlong n (actualAmbientExceptionalDifference (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) T') π')
    (hπ : IsBlowupAlong n (actualAmbientExceptionalDifference W E T) π) :
    ∃ e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso Φ (.step T' _ π' hπ') (.step T _ π hπ) e ∧
      (∀ z,π (e z)=χ (π' z)) ∧
      ∀ k : Z' → Z,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ k →
        (∀ z,π (k z)=χ (π' z)) → k=e := by
  have hC := (original_curve_difference_biholo_isTowerIso hn Φ hW hE hdense hr hiso hT).symm
  have hπ'' : IsBlowupAlong n (χ ⁻¹' actualAmbientExceptionalDifference W E T) π' := hC ▸ hπ'
  obtain ⟨e,hcomm,huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
  exact ⟨e,IsTowerIso.step hiso hπ' hπ e hcomm hC,hcomm,huniq⟩

end
end Hironaka.HironakaSharpActualCurveBaseBiholomorphism
