/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveDefectRestriction
import Hironaka.Blowup.BlowupUniqueness

/-! Genuine stage centre transport and actual unique next blowup comparisons.
No centre equality or desired next map is supplied by original curve consumers. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStageComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveDefectRestriction HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualOriginalControlledHistory
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerIsomorphism
  MarkedIdealRestrictOpen HomogenizedGlueingTower NonmonomialOrderLocal IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Y' Z Z' : CMfd.{u} n}

private theorem actual_marked_identity_pullback (M : MarkedIdeal n X) (hc : M.ideal.IsCoherent) :
    MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M=M := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · simp [MarkedIdeal.pullback]
  · exact BlowupControlledTransform.pullback_id hc

/-- Genuine original domain, actual identity record and real tower TEST
transport precede both directions of the actual FIRST-Z stage dictionary. -/
theorem original_curve_first_defect_isTowerIso (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ)
    (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    chronologicalDistinctDefect W E T'=χ ⁻¹' chronologicalDistinctDefect W E T := by
  let M := originalMemberProductMarked W E 1
  have hM : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hId := actual_marked_identity_pullback M hM.isWellFormed.isCoherent
  have hT' := (IsTowerIso.isGeoTestTower_iff _ hW hM.isWellFormed.isCoherent hiso).mpr hT
  rw [hId] at hT'
  rw [original_curve_first_defect_eq_ordGe_two hn hW hE hdense hr T' hT',
    original_curve_first_defect_eq_ordGe_two hn hW hE hdense hr T hT]
  ext z
  have he := mem_ordGe_geoTransformAlong_isTowerIso hn _ hM hiso hT 2 z
  rw [hId] at he
  exact he

/-- Independent literal original I/J support and WHOLE actual template/strict
transport supply Delta naturality, retaining every ordered exceptional entry. -/
theorem original_curve_actual_difference_isTowerIso (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ)
    (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    actualAmbientExceptionalDifference W E T'=χ ⁻¹' actualAmbientExceptionalDifference W E T := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hT' := (IsTowerIso.isGeoTestTower_iff _ hW hwM.isCoherent hiso).mpr hT
  rw [actual_marked_identity_pullback _ hwM.isCoherent] at hT'
  rw [original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T' hT',
    original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT]
  have hGeom := actual_original_test_history_template _ hwM T hT
  have hRecord := IsTowerIso.geoTransformAlong_eq _ hW isCoherent_unitIdeal hiso hGeom
  rw [actual_marked_identity_pullback _ isCoherent_unitIdeal] at hRecord
  change geoTransformAlong (geometricTemplate W []) T'=MarkedIdeal.pullback χ
    (geoTransformAlong (geometricTemplate W []) T) at hRecord
  have hN := congrArg MarkedIdeal.N hRecord
  have hE' := congrArg MarkedIdeal.E hRecord
  rw [hN,hE']
  have hStrict (H : Set X) : strictAlong T' H=χ ⁻¹' strictAlong T H := by
    simpa using hiso.strictAlong_eq H
  simp_rw [hStrict]
  ext z
  simp [MarkedIdeal.pullback]

/-- Real matching-centre blowup universality constructs a BOTH-sided genuine
biholomorphism and uniqueness among all actual holomorphic commuting maps. -/
theorem exists_unique_stage_blowup_comparison
    (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {C : Set Y} {π' : Z' → Y'} {π : Z → Y}
    (hπ' : IsBlowupAlong n (χ ⁻¹' C) π') (hπ : IsBlowupAlong n C π) :
    ∃ e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      (∀ z,π (e z)=χ (π' z)) ∧
      ∀ k : Z' → Z,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ k →
        (∀ z,π (k z)=χ (π' z)) → k=e := by
  have hρ := isBlowupAlong_comp_inverse χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply hπ
  obtain ⟨e,f,he,hf,hρe,_hπf,hfe,hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ' hρ
  let d : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z :=
    { toFun := e, invFun := f, left_inv := congrFun hfe, right_inv := congrFun hef,
      contMDiff_toFun := he,contMDiff_invFun := hf }
  refine ⟨d,?_,?_⟩
  · intro z
    change π (e z)=χ (π' z)
    have h := congrArg χ (congrFun hρe z)
    simpa only [Function.comp_apply,χ.apply_symm_apply] using h
  · intro k hk hcomm
    obtain ⟨k0,_hk0,huniq⟩ := BlowupUniqueness.existsUnique_comparison hπ' hρ
    have hkρ : (χ.symm ∘ π) ∘ k=π' := by
      funext z
      simp only [Function.comp_apply,hcomm,χ.symm_apply_apply]
    exact (huniq k ⟨hk,hkρ⟩).trans (huniq e ⟨he,hρe⟩).symm

/-- The centre match is PRODUCED from actual FIRST-Z naturality before the
unique new comparison and genuine extended tower isomorphism are constructed. -/
theorem exists_original_curve_first_defect_stage_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ)
    (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {π' : Z' → Y'} {π : Z → Y}
    (hπ' : IsBlowupAlong n (chronologicalDistinctDefect W E T') π')
    (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E T) π) :
    ∃ e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (.step T' (chronologicalDistinctDefect W E T') π' hπ')
        (.step T (chronologicalDistinctDefect W E T) π hπ) e ∧
      (∀ z,π (e z)=χ (π' z)) ∧
      ∀ k : Z' → Z,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ k →
        (∀ z,π (k z)=χ (π' z)) → k=e := by
  have hC := (original_curve_first_defect_isTowerIso hn hW hE hdense hr hiso hT).symm
  have hπ'' : IsBlowupAlong n (χ ⁻¹' chronologicalDistinctDefect W E T) π' := hC ▸ hπ'
  obtain ⟨e,hcomm,huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
  exact ⟨e,IsTowerIso.step hiso hπ' hπ e hcomm hC,hcomm,huniq⟩

/-- The same actual construction uses the independent literal Delta, not an
order cut or a supplied equality of exceptional difference centres. -/
theorem exists_original_curve_difference_stage_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {T' : BlowupTower X Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ)
    (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {π' : Z' → Y'} {π : Z → Y}
    (hπ' : IsBlowupAlong n (actualAmbientExceptionalDifference W E T') π')
    (hπ : IsBlowupAlong n (actualAmbientExceptionalDifference W E T) π) :
    ∃ e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (.step T' (actualAmbientExceptionalDifference W E T') π' hπ')
        (.step T (actualAmbientExceptionalDifference W E T) π hπ) e ∧
      (∀ z,π (e z)=χ (π' z)) ∧
      ∀ k : Z' → Z,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ k →
        (∀ z,π (k z)=χ (π' z)) → k=e := by
  have hC := (original_curve_actual_difference_isTowerIso hn hW hE hdense hr hiso hT).symm
  have hπ'' : IsBlowupAlong n (χ ⁻¹' actualAmbientExceptionalDifference W E T) π' := hC ▸ hπ'
  obtain ⟨e,hcomm,huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
  exact ⟨e,IsTowerIso.step hiso hπ' hπ e hcomm hC,hcomm,huniq⟩

end
end Hironaka.HironakaSharpActualCurveStageComparison
