/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveWholeBoundaryTransversality

/-! Actual centre support and genuine composite isomorphism for the SAME
original two-phase curve history. FIRST-Z remains distinct from sharp Sigma. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveTwoPhaseIsomorphism
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveWholeBoundaryTransversality HironakaSharpActualCurveTwoPhaseDefectErasure
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveWholeAmbientDifferenceCentre
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualOriginalDynamicStep HironakaSharpOriginalProductTraceOrder
  HironakaCoherentTransformExtension NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Both genuine new-difference and actual differential-exceptional support
are localized by the literal recipe, without a centre-support certificate. -/
theorem actual_difference_tail_support_and_exceptional (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),actualAmbientDifferenceSteps W E P S →
      actualAmbientExceptionalDifference W E (P.append S) ⊆ S.proj ⁻¹' actualAmbientExceptionalDifference W E P ∧
      exceptionalLocus n S.proj ⊆ S.proj ⁻¹' actualAmbientExceptionalDifference W E P
  | _,.refl,_ => by
    refine ⟨Subset.rfl,?_⟩
    simp only [BlowupTower.proj_refl,exceptionalLocus_id,empty_subset]
  | _,.step S C π hπ,hs => by
    obtain ⟨hs,hCeq⟩ := hs
    subst C
    obtain ⟨hD,hExc⟩ := actual_difference_tail_support_and_exceptional hn hW hE hdense hr P hP S hs
    have hTest := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hs
    have hNew := original_curve_new_ambient_difference_over_old hn hW hE hdense hr (P.append S) hTest hπ
    refine ⟨fun z hz => hD (hNew hz),?_⟩
    change exceptionalLocus n (S.proj ∘ π) ⊆ _
    rw [exceptionalLocus_comp (S.contMDiff_proj.mdifferentiable (by simp))
      (hπ.contMDiff.mdifferentiable (by simp))]
    rintro z (hz | hz)
    · exact hD (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hz)
    · exact hExc hz

/-- Actual full first-step difference support, independently of final
emptiness, gives a genuine WHOLE composite isomorphism over initial FIRST-Z^c. -/
theorem actual_first_defect_then_difference_tail_isomorphism (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {π : Y → X} (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π)
    (hFirst : IsGeoTestTower (originalMemberProductMarked W E 1)
      (.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ))
    (S : BlowupTower Y Z)
    (hs : actualAmbientDifferenceSteps W E
      (.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ) S) :
    let T := (BlowupTower.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ).append S
    T.proj '' exceptionalLocus n T.proj ⊆ chronologicalDistinctDefect W E (.refl : BlowupTower X X) ∧
      IsIsomorphismOver n T.proj (chronologicalDistinctDefect W E (.refl : BlowupTower X X))ᶜ := by
  let C := chronologicalDistinctDefect W E (.refl : BlowupTower X X)
  let P := BlowupTower.step .refl C π hπ
  have hFirstSupport : actualAmbientExceptionalDifference W E P ⊆ π ⁻¹' C := by
    have he := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr P hFirst
    intro y hy
    have hF := (he ▸ hy).1.2
    change y ∈ ⋃ H ∈ [π ⁻¹' C],H at hF
    simpa only [List.mem_singleton,iUnion_iUnion_eq_left] using hF
  have hTail := (actual_difference_tail_support_and_exceptional hn hW hE hdense hr P hFirst S hs).2
  have hProj : (P.append S).proj=π ∘ S.proj := by
    simp only [P,BlowupTower.proj_append,BlowupTower.proj_step,BlowupTower.proj_refl,Function.id_comp]
  have hExc : (P.append S).proj '' exceptionalLocus n (P.append S).proj ⊆ C := by
    rintro _ ⟨z,hz,rfl⟩
    rw [hProj] at hz ⊢
    rw [exceptionalLocus_comp (hπ.contMDiff.mdifferentiable (by simp))
      (S.contMDiff_proj.mdifferentiable (by simp))] at hz
    rcases hz with hz | hz
    · exact hFirstSupport (hTail hz)
    · exact BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hz
  exact ⟨hExc,HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    (P.append S).isBlowupSequence hExc⟩

/-- ONLY original curve inputs and compact initial cosupport construct ONE
actual original history with true full transversality and same-P isomorphism. -/
theorem exists_original_curve_two_phase_transverse_isomorphism (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (hK : IsCompact (originalMemberProductMarked W E 1).cosupp) :
    ∃ (Z : CMfd.{u} n) (T : BlowupTower X Z),
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧
      chronologicalDistinctDefect W E T=∅ ∧ actualAmbientExceptionalDifference W E T=∅ ∧
      IsProperMap T.proj ∧ IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1) T) ∧
      IsSNCDivisor n (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) ∧
      IsTransverse n (geoTransformAlong (geometricTemplate W []) T).N
        (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) ∧
      IsIsomorphismOver n T.proj (chronologicalDistinctDefect W E (.refl : BlowupTower X X))ᶜ := by
  obtain ⟨Y',π,hπ,Z,S,hs,hTest,hFirst,hDelta,hProper,hDom,_hSNC⟩ :=
    exists_original_curve_two_actual_defect_erasure_phases hn hW hE hdense hr .refl trivial hK
  let P := BlowupTower.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ
  have hP : IsGeoTestTower (originalMemberProductMarked W E 1) P := (isGeoTestTower_append_iff _ P S).mp hTest |>.1
  exact ⟨Z,P.append S,hTest,hFirst,hDelta,hProper,hDom,
    original_curve_whole_ambient_boundary_isSNC hn hW hE hdense hr _ hTest,
    original_curve_two_empty_defects_whole_boundary_transverse hn hW hE hdense hr _ hTest hFirst hDelta,
    (actual_first_defect_then_difference_tail_isomorphism hn hW hE hdense hr hπ hP S hs).2⟩

end
end Hironaka.HironakaSharpActualCurveTwoPhaseIsomorphism
