/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGluedProjection

/-! Only original curve data construct the actual covering sharp recipes
and their genuine pairwise stagewise comparisons, with no input certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveOriginalRecipeAtlas
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveRetainedLocalRecipes HironakaSharpActualCurveOverlapMaps
  HironakaSharpActualCurveCommonOpenCocycle HironakaSharpActualCurveChosenOverlapCocycle
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalDeepProductBlowup HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalMemberProductDomain HironakaSharpActualFiniteChronologicalHistory
  HomogenizedGlueingTower MarkedIdealBiholomorphism
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual OUTPUT witnesses, constructed below from ONLY original inputs.
All true recipe and endpoint geometry remain on these SAME witnesses. -/
structure ActualLocalSharpRecipe (W : Set X) (E : List (Set X)) (x : X) where
  openSet : Opens X
  point_mem : x∈openSet
  prefixSpace : CMfd.{u} n
  firstMap : prefixSpace → CMfd.of (n := n) openSet
  firstBlowup : IsBlowupAlong n
    (chronologicalDistinctDefect ((Subtype.val : openSet → X) ⁻¹' W)
      (E.map ((Subtype.val : openSet → X) ⁻¹' ·))
      (.refl : BlowupTower (CMfd.of (n := n) openSet) (CMfd.of (n := n) openSet))) firstMap
  finalSpace : CMfd.{u} n
  tailTower : BlowupTower prefixSpace finalSpace
  geometry :
    let WU := (Subtype.val : openSet → X) ⁻¹' W
    let EU := E.map ((Subtype.val : openSet → X) ⁻¹' ·)
    let P := BlowupTower.step .refl _ firstMap firstBlowup
    MarkedIdeal.pullback (Subtype.val : openSet → X) (originalMemberProductMarked W E 1)=
      originalMemberProductMarked (X := CMfd.of (n := n) openSet) WU EU 1 ∧
    actualAmbientDifferenceSteps WU EU P tailTower ∧
    IsGeoTestTower (originalMemberProductMarked (X := CMfd.of (n := n) openSet) WU EU 1) (P.append tailTower) ∧
    chronologicalDistinctDefect WU EU (P.append tailTower)=∅ ∧
    actualAmbientExceptionalDifference WU EU (P.append tailTower)=∅ ∧
    IsProperMap (P.append tailTower).proj ∧
    IsInvDomain 1 (geoTransformAlong
      (originalMemberProductMarked (X := CMfd.of (n := n) openSet) WU EU 1) (P.append tailTower)) ∧
    IsSNCDivisor n (EU.map (strictAlong (P.append tailTower)) ++
      (geoTransformAlong (geometricTemplate WU []) (P.append tailTower)).E) ∧
    IsTransverse n (geoTransformAlong (geometricTemplate WU []) (P.append tailTower)).N
      (EU.map (strictAlong (P.append tailTower)) ++
        (geoTransformAlong (geometricTemplate WU []) (P.append tailTower)).E) ∧
    IsIsomorphismOver n (P.append tailTower).proj (originalGoodLocus (n := n) WU EU)

abbrev ActualLocalSharpRecipe.firstTower {W : Set X} {E : List (Set X)} {x : X}
    (R : ActualLocalSharpRecipe W E x) : BlowupTower (CMfd.of (n := n) R.openSet) R.prefixSpace :=
  .step .refl _ R.firstMap R.firstBlowup

/-- Every actual open, first blowup, terminating literal tail and geometry
comes from the genuine original-only local producer, including outside W. -/
def originalLocalSharpRecipe (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (x : X) : ActualLocalSharpRecipe W E x := by
  apply Classical.choice
  obtain ⟨U,hx,hWhole,Y,π,hπ,Z,S,hSteps,hTest,hZ,hD,hProper,hDom,hSNC,hTrans,hGood⟩ :=
    exists_original_curve_retained_local_recipe hn hW hE hdense hr x
  exact ⟨⟨U,hx,Y,π,hπ,Z,S,hWhole,hSteps,hTest,hZ,hD,hProper,hDom,hSNC,hTrans,hGood⟩⟩

/-- Genuine comparisons are produced for the SAME retained original
recipes, at the internal sum cut; no caller comparison or cover is used. -/
def originalEndpointHistories (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) : ActualEndpointHistories X X := by
  let R := originalLocalSharpRecipe hn hW hE hdense hr
  have hc : ∀ i j : X, ∃ e :
      localEndpoint (R i).openSet ((R i).openSet⊓(R j).openSet) (R i).firstTower (R i).tailTower
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          localEndpoint (R j).openSet ((R i).openSet⊓(R j).openSet) (R j).firstTower (R j).tailTower,
      IsTowerIso (commonOpenBase (R i).openSet (R j).openSet ((R i).openSet⊓(R j).openSet)
        inf_le_left inf_le_right)
        (localPaddedHistory (R i).openSet ((R i).openSet⊓(R j).openSet)
          (R i).firstTower (R i).tailTower ((R i).tailTower.length+(R j).tailTower.length))
        (localPaddedHistory (R j).openSet ((R i).openSet⊓(R j).openSet)
          (R j).firstTower (R j).tailTower ((R i).tailTower.length+(R j).tailTower.length)) e := by
    intro i j
    obtain ⟨e,he,_hUnique⟩ := exists_unique_actual_overlap_recipe_comparison hn hW hE hdense hr
      (R i).openSet (R j).openSet (R i).firstBlowup (R j).firstBlowup
      (R i).tailTower (R j).tailTower (R i).geometry.2.1 (R j).geometry.2.1
      (R i).geometry.2.2.2.2.1 (R j).geometry.2.2.2.2.1
      ((R i).tailTower.length+(R j).tailTower.length) (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact ⟨e,by simpa only [localPaddedHistory,paddedHistory,length_restrict] using he⟩
  exact {
    openSet := fun x => (R x).openSet
    prefixSpace := fun x => (R x).prefixSpace
    finalSpace := fun x => (R x).finalSpace
    prefixTower := fun x => (R x).firstTower
    tail := fun x => (R x).tailTower
    cut := fun i j => (R i).tailTower.length+(R j).tailTower.length
    left_bound := fun _ _ => Nat.le_add_right _ _
    right_bound := fun _ _ => Nat.le_add_left _ _
    comparison := fun i j => Classical.choose (hc i j)
    stagewise := fun i j => Classical.choose_spec (hc i j) }

theorem originalEndpointHistories_point_mem (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (x : X) :
    x∈(originalEndpointHistories hn hW hE hdense hr).openSet x :=
  (originalLocalSharpRecipe hn hW hE hdense hr x).point_mem

theorem originalEndpointHistories_cover (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) :
    ∀ x : X,∃ i : X,x∈(originalEndpointHistories hn hW hE hdense hr).openSet i :=
  fun x => ⟨x,originalEndpointHistories_point_mem hn hW hE hdense hr x⟩

/-- The comparison-family interface retains the actual original first map,
literal recipe and ALL sharp geometry on its own actual prefix/tail witnesses. -/
theorem originalEndpointHistories_geometric_dictionary (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (x : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let U := A.openSet x
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let P := A.prefixTower x
    let S := A.tail x
    ∃ (π : A.prefixSpace x → CMfd.of (n := n) U)
      (hπ : IsBlowupAlong n (chronologicalDistinctDefect WU EU
        (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))) π),
      P=BlowupTower.step .refl _ π hπ ∧
      MarkedIdeal.pullback (Subtype.val : U → X) (originalMemberProductMarked W E 1)=
        originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1 ∧
      actualAmbientDifferenceSteps WU EU P S ∧
      IsGeoTestTower (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1) (P.append S) ∧
      chronologicalDistinctDefect WU EU (P.append S)=∅ ∧
      actualAmbientExceptionalDifference WU EU (P.append S)=∅ ∧
      IsProperMap (P.append S).proj ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1) (P.append S)) ∧
      IsSNCDivisor n (EU.map (strictAlong (P.append S)) ++
        (geoTransformAlong (geometricTemplate WU []) (P.append S)).E) ∧
      IsTransverse n (geoTransformAlong (geometricTemplate WU []) (P.append S)).N
        (EU.map (strictAlong (P.append S)) ++ (geoTransformAlong (geometricTemplate WU []) (P.append S)).E) ∧
      IsIsomorphismOver n (P.append S).proj (originalGoodLocus (n := n) WU EU) := by
  let R := originalLocalSharpRecipe hn hW hE hdense hr x
  exact ⟨R.firstMap,R.firstBlowup,rfl,R.geometry⟩

end
end Hironaka.HironakaSharpActualCurveOriginalRecipeAtlas
