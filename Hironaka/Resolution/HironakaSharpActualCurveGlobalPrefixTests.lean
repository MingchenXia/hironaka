/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixLocalHistories

/-! Genuine base-open TEST descent precedes unrestricted original global TESTs.
No global admissibility, comparison, or numerical certificate is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalPrefixTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantDriver
  HironakaSharpActualCurveGlobalPrefixLocalHistories HironakaSharpActualCurveGlobalPrefixTowers
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalDeepProductBlowup NormalCrossings
  HironakaSharpActualCurveLocalRangeBiholomorphism
open HomogenizedGlueingTower (strictAlong strictAlong_restrict)
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- Descent uses only actual local TESTs and the true cover, not stage records. -/
theorem isGeoTestTower_of_open_cover (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hcoh : M.ideal.IsCoherent)
    (U : J → Opens X) (hc : ∀ x : X,∃ i : J,x∈U i) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (∀ i,IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (restrict (U i) T)) →
        IsGeoTestTower M T := by
  intro Y T
  induction T with
  | refl => exact fun _ => trivial
  | @step Y Z T C π hπ ih =>
    intro hLocal
    have hHead := ih (fun i => (hLocal i).1)
    have hStage := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hcoh T hHead
    refine ⟨hHead,isAdmissibleCentre_of_forall_exists_opens
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hStage.2 hg) ?_⟩
    intro y
    obtain ⟨i,hi⟩ := hc (T.proj y)
    refine ⟨openPreimage T (U i),hi,?_⟩
    have hAd := (hLocal i).2
    rw [geoTransformAlong_restrict (U i) hN hcoh T hHead] at hAd
    exact hAd

/-- Both directions refer to literal original open pullbacks and actual restrictions. -/
theorem isGeoTestTower_iff_open_cover (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hcoh : M.ideal.IsCoherent)
    (U : J → Opens X) (hc : ∀ x : X,∃ i : J,x∈U i)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    IsGeoTestTower M T ↔
      ∀ i,IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (restrict (U i) T) :=
  ⟨fun hT i => isGeoTestTower_restrict (U i) hN hcoh T hT,
    isGeoTestTower_of_open_cover M hN hcoh U hc T⟩

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original curve geometry supplies the genuine whole global original TEST. -/
theorem originalUniformPositiveTower_test (N : ℕ) :
    IsGeoTestTower (originalMemberProductMarked W E 1)
      (originalUniformPositiveTower hn hW hE hdense hr N) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  have hcoh := isCoherent_originalMemberProduct hn hE
  apply isGeoTestTower_of_open_cover _ hW hcoh A.openSet
    (originalEndpointHistories_cover hn hW hE hdense hr)
  intro x
  rw [pullback_val_originalMemberProductMarked hn W hE 1 (A.openSet x)]
  exact (originalPrefix_local_test_and_readouts hn hW hE hdense hr N x).1

/-- True global TEST supplies the whole carrier/ideal regularity before readouts. -/
theorem originalUniformPositiveTower_carrier_and_coherence (N : ℕ) :
    IsClosedSubmanifold n (geoTransformAlong (originalMemberProductMarked W E 1)
      (originalUniformPositiveTower hn hW hE hdense hr N)).N ∧
    (geoTransformAlong (originalMemberProductMarked W E 1)
      (originalUniformPositiveTower hn hW hE hdense hr N)).ideal.IsCoherent :=
  isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hW
    (isCoherent_originalMemberProduct hn hE) _ (originalUniformPositiveTower_test hn hW hE hdense hr N)

/-- Whole global transformed records pull back along the actual SAME local inclusion. -/
theorem originalUniformPositiveTower_local_record (N : ℕ) (x : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let U := A.openSet x
    let M := originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1
    geoTransformAlong M (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).2=
      MarkedIdeal.pullback (M := originalUniformStageManifold hn hW hE hdense hr (N+1))
        (M' := (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).1)
        (endpointLocalInclusion (uniformStageHistories A (N+1)) x)
        (geoTransformAlong (originalMemberProductMarked W E 1)
          (originalUniformPositiveTower hn hW hE hdense hr N)) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let U := A.openSet x
  have hTest := originalUniformPositiveTower_test hn hW hE hdense hr N
  have hCoh := (originalUniformPositiveTower_carrier_and_coherence hn hW hE hdense hr N).2
  have hRestrict := geoTransformAlong_restrict U hW (isCoherent_originalMemberProduct hn hE) _ hTest
  rw [pullback_val_originalMemberProductMarked hn W hE 1 U] at hRestrict
  have hRead := (originalPrefix_local_test_and_readouts hn hW hE hdense hr N x).2.1
  refine hRead.trans ((congrArg (fun R =>
    MarkedIdeal.pullback (localOriginalPrefixBiholomorphism A hc N x) R) hRestrict).trans ?_)
  exact StepOneTangentChange.pullback_pullback_of_comp
    (P := CMfd.of (n := n) (openPreimage (originalUniformPositiveTower hn hW hE hdense hr N) U))
    (Q := (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).1)
    (Y := originalUniformStageManifold hn hW hE hdense hr (N+1))
    hCoh contMDiff_subtype_val (localOriginalPrefixBiholomorphism A hc N x).contMDiff (fun _ => rfl)

/-- Arbitrary original subsets use the genuine global strict transform, on ENTIRE ranges. -/
theorem originalUniformPositiveTower_local_strict (N : ℕ) (x : X) (S : Set X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let U := A.openSet x
    strictAlong (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).2
      ((Subtype.val : U → X) ⁻¹' S)=
        (endpointLocalInclusion (uniformStageHistories A (N+1)) x) ⁻¹'
          strictAlong (originalUniformPositiveTower hn hW hE hdense hr N) S := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet x
  have hRead := (originalPrefix_local_test_and_readouts hn hW hE hdense hr N x).2.2
    ((Subtype.val : U → X) ⁻¹' S)
  rw [strictAlong_restrict] at hRead
  exact hRead

/-- Original ordered entries are retained separately from the born auxiliary boundary. -/
theorem originalUniformPositiveTower_local_ordered_family (N : ℕ) (x : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let U := A.openSet x
    E.map (fun S => strictAlong (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).2
      ((Subtype.val : U → X) ⁻¹' S))=
        E.map (fun S => (endpointLocalInclusion (uniformStageHistories A (N+1)) x) ⁻¹'
          strictAlong (originalUniformPositiveTower hn hW hE hdense hr N) S) := by
  exact List.map_congr_left (fun S _ => originalUniformPositiveTower_local_strict hn hW hE hdense hr N x S)

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalPrefixTests
