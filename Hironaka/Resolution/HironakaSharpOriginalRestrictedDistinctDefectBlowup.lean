/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalRestrictedDistinctDefectCentre

/-! Actual SAME original restricted FIRST Z maximum has a genuine blowup
preserving EVERY original good NC point. Source-first complete math precedes
this producer; dynamic strict-trace histories and full termination stay open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalRestrictedDistinctDefectBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalRestrictedDistinctDefectCentre HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalDeepProductBlowup
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  BlowupStrictSubmanifold BlowupIsomorphismOff
variable {n : ℕ} {X : CMfd.{u} n}

/-- ONLY original inputs produce actual SAME restricted-Z centre/projection and genuine whole-good geometry. -/
theorem exists_actual_original_restrictedDistinctDefect_blowup (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),C.Nonempty ∧
      (originalMemberProductMarked W E 1).IsAdmissibleCentre C ∧
      C ⊆ originalDistinctDefectPhase W E ∧ C ⊆ originalSharpBadLocus (n := n) W E ∧ C ⊆ W ∩ ⋃ H ∈ E,H ∧
      Disjoint C (originalGoodLocus (n := n) W E) ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (originalGoodLocus (n := n) W E) ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X))
        (originalDistinctDefectPhase W E) := by
  obtain ⟨C,hCne,hCZ,_hCsm,hCadm,_hNCE,hemb,hdis,hCeq⟩ :=
    exists_actual_original_restrictedDistinctDefect_centre hn hW hE hd hreg hdense hcompact hne
  have hbad : C ⊆ originalSharpBadLocus (n := n) W E := hCZ.trans
    (originalDistinctDefectPhase_subset_sharpBad hn hW hE hdense)
  have hboundary : C ⊆ W ∩ ⋃ H ∈ E,H := hbad.trans (originalSharpBadLocus_subset_boundary hW)
  have hdom := originalMemberProductMarked_isInvDomain hn hW hE hd hreg hdense le_rfl
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hdom).subset)
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hint
  have hGsub : originalGoodLocus (n := n) W E ⊆ Cᶜ := fun _ hz hC => Set.disjoint_left.mp hdis hC hz
  have hisoC := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (originalGoodLocus (n := n) W E) := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hisoC.2.mono_left (preimage_mono hGsub)⟩
    · exact hisoC.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨y,_hy,hπy⟩ := hisoC.1.2.2 (hGsub hx)
      exact ⟨y,by change π y ∈ originalGoodLocus (n := n) W E; rwa [hπy],hπy⟩
  have hdenseC : W ⊆ closure (W \ C) := hdense.trans (closure_mono (by
    rintro x ⟨hxW,hxE⟩
    exact ⟨hxW,fun hxC => hxE (hboundary hxC).2⟩))
  have hgeo := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hdenseC
  have hW' : IsClosedSubmanifold n (strictTransform n π W) := by
    rw [← hgeo]
    exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold
      hπ hW (fun _ hz => (hboundary hz).1)
  have hMwell : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      VanishingIdealCoherent.isCoherent_vanishingIdeal hW,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hE' := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hMwell hemb hπ).isSNCDivisor
  exact ⟨C,Y,π,hCne,hCadm,hCZ,hbad,hboundary,hdis,hemb,hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hW',hE',hCeq⟩


end
end Hironaka.HironakaSharpOriginalRestrictedDistinctDefectBlowup
