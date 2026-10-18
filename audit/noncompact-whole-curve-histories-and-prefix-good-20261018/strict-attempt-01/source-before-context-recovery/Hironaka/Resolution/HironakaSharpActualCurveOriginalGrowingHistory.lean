/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveCompactBoundaryReadouts
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence

/-! Actual original GrowingSeq, with whole TESTs before genuine locally finite
next-centre images. No canonical sequence or numerical driver is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveOriginalGrowingHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveGlobalPrefixTests
  HironakaSharpActualCurveFullAmbientBoundary HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalSuccessorCentre
  HironakaSharpActualCurveGlobalSuccessorMap HironakaSharpActualCurveGlobalSuccessorBlowup
  HironakaSharpActualCurveUniformInitialStage HironakaSharpActualCurveLocalStationaryCentres
  HironakaSharpActualCurveCompactSubsetStopping HironakaSharpActualCurveStoppedOpenGluing
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- Every next stage is the SAME actual transported whole-prefix constructor. -/
def uniformGrowingSeq (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) : GrowingSeq X where
  stage k := ⟨(uniformOriginalTransport A hc k).target,(uniformOriginalTransport A hc k).tower⟩
  zero := rfl
  succ _k := ⟨_,_,_,rfl⟩

theorem uniformGrowingSeq_length (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    ((uniformGrowingSeq A hc).stage k).2.length=k :=
  (length_transport (initialProjectionBiholomorphism A hc).symm (uniformGlobalTower A hc k)).trans
    (uniformGlobalTower_length A hc k)

private def lastCentreImage : {Y : CMfd.{u} n} → BlowupTower X Y → Set X
  | _,.refl => ∅
  | _,.step T C _ _ => T.proj '' C

/-- The API's genuinely chosen next centre has the exact actual global image. -/
theorem centreImage_uniformGrowingSeq (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    centreImage (uniformGrowingSeq A hc) k=
      (gluedProjection (uniformStageHistories A k)) '' globalUniformCentre A k := by
  obtain ⟨π,hπ,hStep⟩ := exists_step_map (uniformGrowingSeq A hc) k
  have hRead := congrArg (lastCentreImage (X := X)) hStep
  change lastCentreImage ((uniformGrowingSeq A hc).stage (k+1)).2=
    centreImage (uniformGrowingSeq A hc) k at hRead
  rw [←hRead]
  change (uniformOriginalTransport A hc k).tower.proj ''
    ((uniformOriginalTransport A hc k).back ⁻¹' globalUniformCentre A k)=_
  have hp (y : (uniformOriginalTransport A hc k).target) :
      (uniformOriginalTransport A hc k).tower.proj y=
        gluedProjection (uniformStageHistories A k) ((uniformOriginalTransport A hc k).back y) := by
    have h := proj_transport (initialProjectionBiholomorphism A hc).symm
      (uniformGlobalTower A hc k) y
    have he := congrArg (initialProjectionBiholomorphism A hc) h
    rw [Diffeomorph.apply_symm_apply] at he
    exact he.trans (uniformGlobalTower_projection A hc k _)
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨(uniformOriginalTransport A hc k).back y,hy,(hp y).symm⟩
  · rintro ⟨y,hy,rfl⟩
    refine ⟨(uniformOriginalTransport A hc k).back.symm y,?_,?_⟩
    · exact Eq.mpr (congrArg (fun z => z∈globalUniformCentre A k)
        ((uniformOriginalTransport A hc k).back.apply_symm_apply y)) hy
    · exact (hp _).trans (congrArg (gluedProjection (uniformStageHistories A k))
        ((uniformOriginalTransport A hc k).back.apply_symm_apply y))

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original curve inputs construct the API's genuine original-base sequence. -/
def originalGrowingSeq : GrowingSeq X :=
  uniformGrowingSeq (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr)

theorem originalGrowingSeq_test (k : ℕ) :
    IsGeoTestTower (originalMemberProductMarked W E 1)
      ((originalGrowingSeq hn hW hE hdense hr).stage k).2 := by
  cases k with
  | zero => trivial
  | succ k => exact originalUniformPositiveTower_test hn hW hE hdense hr k

/-- The whole ORIGINAL ordered ambient family has its own independent TEST. -/
theorem originalGrowingSeq_ambient_test (k : ℕ) :
    IsGeoTestTower (geometricTemplate (univ : Set X) E)
      ((originalGrowingSeq hn hW hE hdense hr).stage k).2 ∧
    NormalCrossings.IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E)
      ((originalGrowingSeq hn hW hE hdense hr).stage k).2).E :=
  (original_curve_history_full_ambient_boundary hn hW hE hdense hr _
    (originalGrowingSeq_test hn hW hE hdense hr k)).2

/-- ALL indexed centre images are locally finite, without canonicality. -/
theorem locallyFinite_originalGrowingSeq_centreImage :
    LocallyFinite (centreImage (originalGrowingSeq hn hW hE hdense hr)) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  intro x
  obtain ⟨U,hx,L,hLate⟩ := originalUniformCentres_locally_stationary hn hW hE hdense hr x
  refine ⟨(U : Set X),U.isOpen.mem_nhds hx,?_⟩
  apply (finite_Iio L).subset
  intro k hk
  by_contra h
  obtain ⟨z,hz,hzU⟩ := hk
  rw [show centreImage (originalGrowingSeq hn hW hE hdense hr) k=
    (gluedProjection (uniformStageHistories A k)) '' globalUniformCentre A k from
      centreImage_uniformGrowingSeq A hc k] at hz
  obtain ⟨y,hy,rfl⟩ := hz
  exact disjoint_left.mp (hLate k (Nat.le_of_not_gt h)) hy hzU

/-- Genuine closed centre images and local finiteness give their whole closed union. -/
theorem isClosed_originalGrowingSeq_centreImage_union :
    IsClosed (⋃ k,centreImage (originalGrowingSeq hn hW hE hdense hr) k) :=
  (locallyFinite_originalGrowingSeq_centreImage hn hW hE hdense hr).isClosed_iUnion
    (fun k => isClosed_centreImage _ k)

/-- Ordinary compactness supplies actual eventual avoidance; no global maximum. -/
theorem originalGrowingSeq_compact_encounters (K : Set X) (hK : IsCompact K) :
    (∃ N : ℕ,∀ k,N≤k →
      Disjoint (centreImage (originalGrowingSeq hn hW hE hdense hr) k) K) ∧
    {k | (centreImage (originalGrowingSeq hn hW hE hdense hr) k ∩ K).Nonempty}.Finite := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc K hK
  have hLate (k : ℕ) (hk : N+1≤k) :
      Disjoint (centreImage (originalGrowingSeq hn hW hE hdense hr) k) K := by
    rw [show centreImage (originalGrowingSeq hn hW hE hdense hr) k=
      (gluedProjection (uniformStageHistories A k)) '' globalUniformCentre A k from
        centreImage_uniformGrowingSeq A hc k]
    apply disjoint_left.mpr
    rintro z ⟨y,hy,rfl⟩ hz
    exact disjoint_left.mp (globalCentres_avoid_subset_of_stopped_open A K (N+1) hN k hk) hy hz
  refine ⟨⟨N+1,hLate⟩,(finite_Iio (N+1)).subset ?_⟩
  intro k hk
  by_contra h
  obtain ⟨z,hz,hzK⟩ := hk
  exact disjoint_left.mp (hLate k (Nat.le_of_not_gt h)) hz hzK

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveOriginalGrowingHistory
