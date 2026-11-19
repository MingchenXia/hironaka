/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.OriginalCentresOverAppendHeadExact
import Hironaka.Resolution.HironakaSharpActualCurveLocallyFiniteSharpHistory
import Hironaka.Resolution.HironakaSharpActualCurveGlobalExceptionalBirthSupport

/-! Actual FIRST/Delta recipe support gives every genuine growing centre over
original bad, and every original-boundary admissible prefix preserves good. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGrowingGoodPreservation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  RestrictEmptyTower NormalCrossings NormalCrossingsInvariance
  HironakaAdmissibleSequence HironakaAdmissibleCalculus HironakaLocallyFiniteResolutionSequence
  HironakaSharpActualCurveOriginalGrowingHistory HironakaSharpActualCurveUniformPrefixes
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveUniformSuccessorComparison
  HironakaSharpActualCurveGlobalExceptionalBirthSupport HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualCurveInitialGoodPreservation HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualCurveGlobalGoodIsomorphism
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMemberProductDomain
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem centresOver_mono {F B : Set X} (hFB : F⊆B) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresOver F T → CentresOver B T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,h => ⟨centresOver_mono hFB T h.1,fun _ hy => hFB (h.2 hy)⟩

private theorem centresOver_of_empty (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),ResolutionInvariantExt.IsEmptyTower T → CentresOver F T
  | _,.refl,_ => trivial
  | _,.step T C _ _,h => ⟨centresOver_of_empty F T h.1,by rw [h.2];exact empty_subset _⟩

/-- True heads of actual empty-padded recipes inherit whole centre support. -/
theorem centresOver_uniformPrefix (F : Set X) (T : BlowupTower X Y)
    (hT : CentresOver F T) (k : ℕ) : CentresOver F (uniformPrefix T k).2 := by
  have hEmpty := centresOver_of_empty (T.proj ⁻¹' F) (identityEmptyTail Y k)
    (identityEmptyTail_isEmptyTower Y k)
  exact centresOver_head F (T.append (identityEmptyTail Y k)) T.length
    ((centresOver_append_iff F T _).mpr ⟨hT,hEmpty⟩)

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original geometry supplies the FULL actual local recipe support. -/
theorem original_localRecipe_centresOver_bad (i : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    CentresOver ((Subtype.val : A.openSet i → X) ⁻¹' originalSharpBadLocus (n := n) W E)
      ((A.prefixTower i).append (A.tail i)) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let K := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1
  let C₀ := chronologicalDistinctDefect WU EU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))
  let P := A.prefixTower i
  let S := A.tail i
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
  have hOver : CentresOver C₀ (P.append S) := by
    have hFT : IsGeoTestTower K (.step .refl C₀ π hπ) := hFirst ▸ hFirstTest
    have hST : actualAmbientDifferenceSteps WU EU (.step .refl C₀ π hπ) S := hFirst ▸ hSteps
    have ho := first_difference_recipe_centresOver hn hWU hEU hDenseU hrU hπ hFT S hST
    rw [show P=BlowupTower.step .refl C₀ π hπ from hFirst]
    exact ho
  have hBad : C₀⊆(Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
    intro y hy
    rw [originalSharpBadLocus_eq_compl_good]
    intro hg
    exact original_curve_initial_good_subset_first_defect_complement hn hWU hEU hDenseU hrU
      (originalGoodLocus_preimage_val U y hg) hy
  exact centresOver_mono hBad (P.append S) hOver

/-- ACTUAL global next-centre images, rather than differential exceptional images. -/
theorem original_globalCentre_image_subset_bad (k : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    (gluedProjection (uniformStageHistories A k)) '' globalUniformCentre A k ⊆
      originalSharpBadLocus (n := n) W E := by
  let A := originalEndpointHistories hn hW hE hdense hr
  dsimp only
  rintro x ⟨q,hq,rfl⟩
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A k) q
  let T := (A.prefixTower i).append (A.tail i)
  have hz : z∈(actualUniformSuccessor T k).centre := (mem_globalUniformCentre_iff A k i z).mp hq
  have hOver := centresOver_uniformPrefix
    ((Subtype.val : A.openSet i → X) ⁻¹' originalSharpBadLocus (n := n) W E) T
    (original_localRecipe_centresOver_bad hn hW hE hdense hr i) (k+1)
  rw [(actualUniformSuccessor T k).step_eq] at hOver
  have hLocal := hOver.2 hz
  have hSquare := gluedProjection_local_full (uniformStageHistories A k) i z
  exact Eq.mpr (congrArg (fun x : X => x∈originalSharpBadLocus (n := n) W E) hSquare) hLocal

/-- The SAME actual API-selected centre image has original bad support. -/
theorem originalGrowingSeq_centreImage_subset_bad (k : ℕ) :
    centreImage (originalGrowingSeq hn hW hE hdense hr) k ⊆ originalSharpBadLocus (n := n) W E := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  intro x hx
  exact original_globalCentre_image_subset_bad hn hW hE hdense hr k
    (Eq.mp (congrArg (fun B => x∈B) (centreImage_uniformGrowingSeq A hc k)) hx)

/-- ENTIRE propositions are transported along the real recorded successor equality. -/
theorem originalGrowingSeq_centresOver_bad (k : ℕ) :
    CentresOver (originalSharpBadLocus (n := n) W E) ((originalGrowingSeq hn hW hE hdense hr).stage k).2 := by
  let s := originalGrowingSeq hn hW hE hdense hr
  change CentresOver (originalSharpBadLocus (n := n) W E) (s.stage k).2
  induction k with
  | zero => trivial
  | succ k ih =>
    obtain ⟨π,hπ,hStep⟩ := exists_step_map s k
    have hPair : CentresOver (originalSharpBadLocus (n := n) W E)
        (.step (s.stage k).2 (stepCentre s k) π hπ) :=
      ⟨ih,fun y hy => originalGrowingSeq_centreImage_subset_bad hn hW hE hdense hr k ⟨y,hy,rfl⟩⟩
    exact Eq.mpr (congrArg (fun T : BlowupTower X (s.stage (k+1)).1 =>
      CentresOver (originalSharpBadLocus (n := n) W E) T) hStep) hPair

/-- Whole ORIGINAL ordered ambient-boundary admissibility, not auxiliary E=[]. -/
theorem originalGrowingSeq_admissible_sequence (k : ℕ) :
    let s := originalGrowingSeq hn hW hE hdense hr
    IsAdmissibleBlowupSequence n X E (originalSharpBadLocus (n := n) W E)
      (s.stage k).1 (s.stage k).2.proj
        (geoTransformAlong (geometricTemplate (univ : Set X) E) (s.stage k).2).E :=
  isAdmissibleBlowupSequence_proj (geometricTemplate (univ : Set X) E) _ _
    (originalGrowingSeq_ambient_test hn hW hE hdense hr k).1
    (originalGrowingSeq_centresOver_bad hn hW hE hdense hr k)

/-- EVERY actual prefix is an isomorphism over the ENTIRE original good locus. -/
theorem originalGrowingSeq_good_isomorphism (k : ℕ) :
    IsIsomorphismOver n ((originalGrowingSeq hn hW hE hdense hr).stage k).2.proj
      (originalGoodLocus (n := n) W E) := by
  have h := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl
    (originalGrowingSeq_admissible_sequence hn hW hE hdense hr k)
  have hEq : (originalSharpBadLocus (n := n) W E)ᶜ=originalGoodLocus (n := n) W E := by
    rw [originalSharpBadLocus_eq_compl_good,compl_compl]
  exact Eq.mp (congrArg (fun B => IsIsomorphismOver n
    ((originalGrowingSeq hn hW hE hdense hr).stage k).2.proj B) hEq) h

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGrowingGoodPreservation
