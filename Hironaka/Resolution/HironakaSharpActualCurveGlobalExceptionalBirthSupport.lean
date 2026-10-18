/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalStrictClosure
import Hironaka.Resolution.HironakaAdmissibleCalculus

/-! Actual recipe centre images precede the whole finite and genuinely
global indexed birth-boundary support, retaining every empty position. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalExceptionalBirthSupport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerTransforms HomogenizedGlueingTower RestrictEmptyTower
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalStrictClosure HironakaSharpActualCurveGlobalGoodIsomorphism
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaSharpActualCurveLocallyFiniteBoundary
  HironakaSharpActualCurveGlobalBoundaryCoordinates HironakaSharpActualCurveTwoPhaseIsomorphism
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalMemberProductDomain HironakaSharpActualCurveInitialGoodPreservation
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaAdmissibleSequence HironakaAdmissibleCalculus
  NormalCrossings NormalCrossingsInvariance
variable {n : ℕ} {X Y Z : CMfd.{u} n}
attribute [local instance] endpointChartedSpace

/-- All geometric centre images follow the literal CURRENT Delta recipe;
differential exceptional-image support is not substituted for this assertion. -/
theorem first_difference_recipe_centresOver (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)
    {π : Y → X} (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π)
    (hFirst : IsGeoTestTower (originalMemberProductMarked W E 1)
      (.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ)) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),
      actualAmbientDifferenceSteps W E
        (.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ) S →
      CentresOver (chronologicalDistinctDefect W E (.refl : BlowupTower X X))
        ((BlowupTower.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ).append S)
  | _,.refl,_ => ⟨trivial,fun _ hx => hx⟩
  | _,.step S C ρ hρ,hs => by
    obtain ⟨hs,hCeq⟩ := hs
    subst C
    refine ⟨first_difference_recipe_centresOver hn hW hE hdense hr hπ hFirst S hs,?_⟩
    intro z hz
    let C₀ := chronologicalDistinctDefect W E (.refl : BlowupTower X X)
    let P := BlowupTower.step .refl C₀ π hπ
    have hD := (actual_difference_tail_support_and_exceptional hn hW hE hdense hr P hFirst S hs).1 hz
    have he := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr P hFirst
    have hF := (he ▸ hD).1.2
    change S.proj z∈⋃ H∈[π ⁻¹' C₀],H at hF
    change (P.append S).proj z∈C₀
    rw [BlowupTower.proj_append]
    change π (S.proj z)∈C₀
    simpa only [List.mem_singleton,iUnion_iUnion_eq_left,mem_preimage] using hF

/-- The actual append offset, including its empty defaults, preserves
every natural birth position. -/
theorem boundaryReadout_append_offset {A : Type u} (E F : List (Set A)) (j : ℕ) :
    boundaryReadout (E++F) (E.length+j)=boundaryReadout F j := by
  unfold boundaryReadout
  rw [List.getD_append_right E F ∅ _ (Nat.le_add_right _ _),Nat.add_sub_cancel_left]

theorem mem_readout_union_iff {A : Type u} (E : List (Set A)) (z : A) :
    (∃ j,z∈boundaryReadout E j) ↔ z∈⋃ H∈E,H := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hlt : j<E.length
    · rw [boundaryReadout,List.getD_eq_get E ∅ ⟨j,hlt⟩] at hj
      exact mem_iUnion₂.mpr ⟨E.get ⟨j,hlt⟩,List.get_mem E _,hj⟩
    · rw [boundaryReadout,List.getD_eq_default E ∅ (Nat.le_of_not_gt hlt)] at hj
      exact False.elim hj
  · intro hz
    obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hz
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    refine ⟨i,?_⟩
    rw [boundaryReadout,List.getD_eq_get E ∅ i]
    exact hzH

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- Actual whole-list decomposition identifies EVERY natural birth offset
with the SAME empty-initial-boundary original product transform. -/
theorem original_localBirthReadout (i : X) (j : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let U := A.openSet i
    let K := originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1
    localBoundaryReadout A E i (E.length+j)=
      boundaryReadout (geoTransformAlong K ((A.prefixTower i).append (A.tail i))).E j := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let K := originalMemberProductMarked (X := CMfd.of (n := n) U)
    ((Subtype.val : U → X) ⁻¹' W) EU 1
  let M := geometricTemplate (X := CMfd.of (n := n) U) univ EU
  let T := (A.prefixTower i).append (A.tail i)
  have hEq := boundary_geoTransformAlong_decomposition M K rfl T
  change boundaryReadout (geoTransformAlong M T).E (E.length+j)=_
  rw [hEq]
  simpa only [M,EU,geometricTemplate,List.length_map] using
    boundaryReadout_append_offset (EU.map (strictAlong T)) (geoTransformAlong K T).E j

/-- Genuine prefixwise centre images and the original finite admissible
sequence theorem supply both whole local support inclusions. -/
theorem original_localBirth_support (i : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let T := (A.prefixTower i).append (A.tail i)
    exceptionalLocus n T.proj ⊆ ⋃ j,localBoundaryReadout A E i (E.length+j) ∧
      (⋃ j,localBoundaryReadout A E i (E.length+j)) ⊆
        T.proj ⁻¹' ((Subtype.val : A.openSet i → X) ⁻¹' originalSharpBadLocus (n := n) W E) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let K := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1
  let C₀ := chronologicalDistinctDefect WU EU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))
  let P := A.prefixTower i
  let S := A.tail i
  let T := P.append S
  obtain ⟨π,hπ,hFirst,_hPB,hSteps,hTest,_hZ,_hD,_hProper,_hDom,_hSNC,_hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hWU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hrU : ∀ y∈WU,RegularAtDim (n := n) WU y 1 :=
    fun y hy => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr y.val hy)
  have hDenseU : WU⊆closure (WU \ ⋃ H∈EU,H) := by
    intro y hy
    have hp : y∈(Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H∈E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H∈E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  have hFirstTest := ((isGeoTestTower_append_iff K P S).mp hTest).1
  have hOver : CentresOver C₀ T := by
    have hFT : IsGeoTestTower K (.step .refl C₀ π hπ) := hFirst ▸ hFirstTest
    have hST : actualAmbientDifferenceSteps WU EU (.step .refl C₀ π hπ) S := hFirst ▸ hSteps
    have ho := first_difference_recipe_centresOver hn hWU hEU hDenseU hrU hπ hFT S hST
    change CentresOver C₀ (P.append S)
    rw [show P=BlowupTower.step .refl C₀ π hπ from hFirst]
    exact ho
  have hAdm := isAdmissibleBlowupSequence_proj K C₀ T hTest hOver
  have hSupport := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hAdm
  have hSupport' : exceptionalLocus n T.proj ⊆ ⋃ H∈(geoTransformAlong K T).E,H ∧
      (⋃ H∈(geoTransformAlong K T).E,H) ⊆ T.proj ⁻¹' C₀ := by
    simpa only [K,originalMemberProductMarked,List.length_nil,List.drop_zero] using hSupport
  have hOffset : (⋃ j,localBoundaryReadout A E i (E.length+j))=⋃ H∈(geoTransformAlong K T).E,H := by
    have hIndividual : ∀ j,localBoundaryReadout A E i (E.length+j)=
        boundaryReadout (geoTransformAlong K T).E j :=
      fun j => original_localBirthReadout hn hW hE hdense hr i j
    simp_rw [hIndividual]
    ext z
    exact mem_iUnion.trans (mem_readout_union_iff _ z)
  have hBad : C₀⊆(Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
    intro y hy
    rw [originalSharpBadLocus_eq_compl_good]
    intro hg
    have hgU := originalGoodLocus_preimage_val U y hg
    exact original_curve_initial_good_subset_first_defect_complement hn hWU hEU hDenseU hrU hgU hy
  change exceptionalLocus n T.proj ⊆ _ ∧ _
  rw [hOffset]
  exact ⟨hSupport'.1,fun z hz => hBad (hSupport'.2 hz)⟩

/-- ONLY original inputs give the whole actual global exceptional/birth
support inclusions, with every indexed and empty birth retained. -/
theorem original_globalExceptional_birth_support :
    exceptionalLocus n (originalEndpointProjection hn hW hE hdense hr) ⊆
        ⋃ j,originalGluedBoundaryReadout hn hW hE hdense hr (E.length+j) ∧
      (⋃ j,originalGluedBoundaryReadout hn hW hE hdense hr (E.length+j)) ⊆
        (originalEndpointProjection hn hW hE hdense hr) ⁻¹' originalSharpBadLocus (n := n) W E := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  constructor
  · intro q hq
    obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
    have hTrace := preimage_exceptionalLocus_gluedProjection A hc i
    have hMember := congrArg (fun B : Set (A.finalSpace i) => z∈B) hTrace
    have hz : z∈exceptionalLocus n ((A.prefixTower i).append (A.tail i)).proj :=
      Eq.mp hMember hq
    obtain ⟨j,hj⟩ := mem_iUnion.mp ((original_localBirth_support hn hW hE hdense hr i).1 hz)
    exact mem_iUnion.mpr ⟨j,(mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i (E.length+j) z).mpr hj⟩
  · intro q hq
    obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
    obtain ⟨j,hj⟩ := mem_iUnion.mp hq
    have hz := (mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i (E.length+j) z).mp hj
    have hBad := (original_localBirth_support hn hW hE hdense hr i).2 (mem_iUnion.mpr ⟨j,hz⟩)
    change gluedProjection A (endpointLocalInclusion A i z)∈originalSharpBadLocus (n := n) W E
    rw [gluedProjection_local_full]
    exact hBad

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalExceptionalBirthSupport
