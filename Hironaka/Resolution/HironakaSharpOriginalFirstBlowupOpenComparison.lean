/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalFirstDefectOpenNaturality
import Hironaka.Resolution.HironakaSharpOriginalRestrictedDistinctDefectBlowup
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
/-! Actual first sharp maximum blowups on active and silent opens.
All comparisons are genuine blowup lifts; the silent exceptional entry remains. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalFirstBlowupOpenComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen BlowupStrictSubmanifold
  HironakaSharpOriginalFirstDefectOpenNaturality HironakaSharpOriginalRestrictedDistinctDefectBlowup
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaNormalCrossingsSeparationChoiceComparison
  HironakaNormalCrossingsOpenRestrictionSeparation NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres ResolutionDriver
variable {n : ℕ} {X Y : CMfd.{u} n} {C : Set X} {π : Y → X}

/-- The actual entire source of the open-restricted projection. -/
def firstBlowupSourceOpen (hπ : IsBlowupAlong n C π) (U : Opens X) : Opens Y :=
  ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩

/-- The SAME actual projection with its genuine source and target open subtypes. -/
def firstBlowupOpenProjection (hπ : IsBlowupAlong n C π) (U : Opens X) :
    CMfd.of (n := n) (firstBlowupSourceOpen hπ U) → CMfd.of (n := n) U :=
  fun z => ⟨π z.val,z.property⟩

private theorem actual_open_blowup (hπ : IsBlowupAlong n C π) (U : Opens X) :
    IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' C) (firstBlowupOpenProjection hπ U) :=
  isBlowupAlong_restrict hπ U _

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  {d : ℕ} (hd : d+1≤n) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
  (hdense : W⊆closure (W \ ⋃ H∈E,H))

include hW hE hd hreg hdense

/-- Genuine actual meeting of the true maximum identifies the WHOLE local centre. -/
theorem original_first_blowup_open_active (hπ : IsBlowupAlong n C π)
    (hC : C=maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E)) (U : Opens X)
    (hne : ((Subtype.val : U → X) ⁻¹' C).Nonempty) :
    IsBlowupAlong n (maxLocus ((invFamily hn (n+1)).inv
      (originalMemberProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) .refl)
      (originalDistinctDefectPhase (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))))
      (firstBlowupOpenProjection hπ U) := by
  have hmax := original_first_maximum_open_of_meeting hn hW hE hd hreg hdense U (hC ▸ hne)
  rw [←hC] at hmax
  rw [hmax]
  exact actual_open_blowup hπ U

/-- ANY independent local blowup of the true local maximum has one genuine lift. -/
theorem original_first_blowup_open_unique_comparison (hπ : IsBlowupAlong n C π)
    (hC : C=maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E)) (U : Opens X)
    (hne : ((Subtype.val : U → X) ⁻¹' C).Nonempty)
    {Z : CMfd.{u} n} {σ : Z → CMfd.of (n := n) U}
    (hσ : IsBlowupAlong n (maxLocus ((invFamily hn (n+1)).inv
      (originalMemberProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) .refl)
      (originalDistinctDefectPhase (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)))) σ) :
    ∃! e : CMfd.of (n := n) (firstBlowupSourceOpen hπ U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      ∀ z,σ (e z)=firstBlowupOpenProjection hπ U z :=
  exists_unique_lift (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
    (original_first_blowup_open_active hn hW hE hd hreg hdense hπ hC U hne) hσ rfl
end OriginalInput

/-- Actual empty projection, closed strict carrier and literal old++NEW-empty list. -/
theorem original_first_blowup_open_silent (hπ : IsBlowupAlong n C π) (U : Opens X)
    (hempty : (Subtype.val : U → X) ⁻¹' C=∅) {H : Set U} (hH : IsClosed H)
    (F : List (Set U)) (hF : ∀ A∈F,IsClosed A) :
    (∃ e : CMfd.of (n := n) (firstBlowupSourceOpen hπ U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
      ∀ z,e z=firstBlowupOpenProjection hπ U z) ∧
    strictTransform n (firstBlowupOpenProjection hπ U) H=(firstBlowupOpenProjection hπ U) ⁻¹' H ∧
    (F.map (geoStrictTransform (firstBlowupOpenProjection hπ U) ((Subtype.val : U → X) ⁻¹' C)) ++
      [(firstBlowupOpenProjection hπ U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C)])=
        F.map ((firstBlowupOpenProjection hπ U) ⁻¹' ·) ++ [∅] := by
  have hR := actual_open_blowup hπ U
  rw [hempty] at hR
  obtain ⟨he,hStrict,hOld,hNew⟩ := empty_blowup_whole_closed_dictionary (A := CMfd.of (n := n) U)
    (B := CMfd.of (n := n) (firstBlowupSourceOpen hπ U)) hR hH F hF
  refine ⟨he,hStrict,?_⟩
  rw [hempty,hOld,hNew]

/-- ONLY original compact pure geometry chooses SAME sharp blowup before ALL opens. -/
theorem exists_original_first_blowup_all_opens (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1≤n) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsIsomorphismOver n π (originalGoodLocus (n := n) W E) ∧
      C=maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
        (originalDistinctDefectPhase W E) ∧
      ∀ U : Opens X,
        (((Subtype.val : U → X) ⁻¹' C).Nonempty →
          IsBlowupAlong n (maxLocus ((invFamily hn (n+1)).inv
            (originalMemberProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
              (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) .refl)
            (originalDistinctDefectPhase (X := CMfd.of (n := n) U)
              ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))))
            (firstBlowupOpenProjection hπ U)) ∧
        ((Subtype.val : U → X) ⁻¹' C=∅ →
          (∃ e : CMfd.of (n := n) (firstBlowupSourceOpen hπ U)
              ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
            ∀ z,e z=firstBlowupOpenProjection hπ U z) ∧
          strictTransform n (firstBlowupOpenProjection hπ U) ((Subtype.val : U → X) ⁻¹' W)=
            (firstBlowupOpenProjection hπ U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W) ∧
          ((E.map ((Subtype.val : U → X) ⁻¹' ·)).map
              (geoStrictTransform (firstBlowupOpenProjection hπ U) ((Subtype.val : U → X) ⁻¹' C)) ++
            [(firstBlowupOpenProjection hπ U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C)])=
              (E.map ((Subtype.val : U → X) ⁻¹' ·)).map
                ((firstBlowupOpenProjection hπ U) ⁻¹' ·) ++ [∅]) := by
  obtain ⟨C,Y,π,hCne,_hadm,_hCZ,_hBad,_hBound,_hDis,hemb,hπ,_hPr,_hHol,hGood,_hSm,_hSNC,hCeq⟩ :=
    exists_actual_original_restrictedDistinctDefect_blowup hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCne,hemb,hGood,hCeq,?_⟩
  intro U
  refine ⟨original_first_blowup_open_active hn hW hE hd hreg hdense hπ hCeq U,?_⟩
  intro hempty
  apply original_first_blowup_open_silent hπ U hempty (hW.1.preimage continuous_subtype_val)
  intro A hA
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
  exact (hE.1 B hB).preimage continuous_subtype_val
end
end Hironaka.HironakaSharpOriginalFirstBlowupOpenComparison
