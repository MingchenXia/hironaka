import Hironaka.Resolution.HironakaG8FiniteCuspSheetSchedule
import Hironaka.Resolution.HironakaG8CuspPointTowerEndpoint

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8SameClockCuspSheets
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupRestrictOpen BlowupTowerIsomorphism BlowupTowerTransforms HironakaG8CuspPointTower HironakaEmbeddedAnalytic MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG3EmptyAwareHistory HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison
  HironakaG8CountableCuspSheets HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource
  HironakaG8FiniteScheduledSheetTest HironakaG8SingularFootprintExtension
  HironakaNormalCrossingsSeparationChoiceComparison HironakaStageCenters NormalCrossings
  HironakaG8DisjointClockAtlas HironakaG8FiniteSingularTowerMerge
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaG8FiniteCuspSheetSchedule
  HironakaG8CuspPointTowerEndpoint

local notation "𝓘c" => 𝓘(ℂ, ComplexModel 3)

/-- An independent simultaneous clock resolves the whole countable union in
three genuine original TEST steps. -/
theorem exists_whole_cusp_sheets_three_step_test :
    ∃ (Z : CMfd.{0} 3) (R : BlowupTower sheetManifold Z),
      R.length = 3 ∧
      IsGeoTestTower (cuspMarked (X := sheetManifold) (sheetCusps (fun _ => 7))) R ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 3)
        (strictTransform 3 P.proj (sheetCusps (fun _ => 7)))) R ∧
      IsClosedSubmanifold 3 (strictTransform 3 R.proj (sheetCusps (fun _ => 7))) ∧
      ∀ j < 3, slotFootprint R j = {x : CuspSheets | x.2 = 0} := by
  obtain ⟨Y,T,hLen,hSmooth,hTest,hStage,hFoot,_⟩ := exists_three_cusp_point_blowups_smooth
  let W := sheetCusps (fun _ => 7)
  have hClosed : IsClosed W := sheetCusps_isClosed _
  let M := cuspMarked (X := sheetManifold) W
  have hM : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      CartanIrreducible.cartanCoherence W (sheetCusps_isAnalytic _), isSNCDivisor_nil,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  have hCover (x : sheetManifold) : ∃ i, x ∈ sheetOpen i := ⟨x.1,mem_singleton _,mem_univ _⟩
  have hDisj : Pairwise fun i j => Disjoint (sheetOpen i : Set sheetManifold) (sheetOpen j) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun _ hi hj =>
      hij ((mem_singleton_iff.mp hi.1).symm.trans (mem_singleton_iff.mp hj.1))
  let S (i : ℕ) := transport (X' := CMfd.of (n := 3) (sheetOpen i))
    (sheetBiholomorph i) T
  have hIso (i : ℕ) : IsTowerIso (sheetBiholomorph i) (S i).tower T (S i).back :=
    transport_isTowerIso (X' := CMfd.of (n := 3) (sheetOpen i)) (sheetBiholomorph i) T
  have hRead (i : ℕ) : (Subtype.val : sheetOpen i → sheetManifold) ⁻¹' W =
      sheetBiholomorph i ⁻¹' embeddedCuspSet 7 := sheetCusps_preimage_sheet _ i
  have hMarked (i : ℕ) :
      MarkedIdeal.pullback (Subtype.val : sheetOpen i → sheetManifold) M =
      MarkedIdeal.pullback (sheetBiholomorph i) (cuspMarked (X := CuspAmbient) (embeddedCuspSet 7)) := by
    have h₁ := pullback_vanishingIdeal_opens (m := 3) (n := 3) (sheetOpen i) (id : sheetOpen i → sheetOpen i) W
    have h₂ := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      (sheetBiholomorph i).contMDiff (sheetBiholomorph i).symm.contMDiff
      (sheetBiholomorph i).apply_symm_apply (sheetBiholomorph i).symm_apply_apply
      (contMDiff_id (I := 𝓘c) (M := sheetOpen i)) (embeddedCuspSet 7)
    rw [hRead] at h₁
    have hI := h₁.symm.trans h₂
    change MarkedIdeal.mk _ _ _ _ = MarkedIdeal.mk _ _ _ _
    congr 1
  have hSTest (i : ℕ) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : sheetOpen i → sheetManifold)
        M) (S i).tower := by
    rw [hMarked]
    exact (isGeoTestTower_transport_iff (X' := CMfd.of (n := 3) (sheetOpen i)) (sheetBiholomorph i)
      (CartanIrreducible.cartanCoherence _ (embedded_cusp_isAnalytic 7)) T).mpr hTest
  have hSStage (i : ℕ) :
      StageCentres (fun P C => C ⊆ singularSet (n := 3)
        (strictTransform 3 P.proj ((Subtype.val : sheetOpen i → sheetManifold) ⁻¹' W))) (S i).tower := by
    apply singular_stages_of_tower_iso (X' := CuspAmbient) _ (hClosed.preimage continuous_subtype_val) (sheetBiholomorph i).symm
      (hIso i).symm
    have hPre : (sheetBiholomorph i).symm ⁻¹'
        ((Subtype.val : sheetOpen i → sheetManifold) ⁻¹' W) = embeddedCuspSet 7 := by
      rw [hRead]
      ext x
      simp only [mem_preimage,Diffeomorph.apply_symm_apply]
    rwa [hPre]
  have hSSmooth (i : ℕ) :
      IsClosedSubmanifold 3 (strictTransform 3 (S i).tower.proj
        ((Subtype.val : sheetOpen i → sheetManifold) ⁻¹' W)) := by
    rw [hRead,strictTransform_preimage_of_square (sheetBiholomorph i) (S i).back
      (S i).tower.contMDiff_proj T.contMDiff_proj _ (embedded_cusp_isAnalytic 7).isClosed
      (fun z => ((hIso i).proj_comm z).symm)]
    exact (isClosedSubmanifold_preimage_iff (S i).back).mpr hSmooth
  obtain ⟨Z,R,hL,hRT,hPatches⟩ := exists_disjoint_clock_test_tower sheetOpen hCover hDisj
    (fun i => (S i).tower) 2 (fun i => (length_transport
      (X' := CMfd.of (n := 3) (sheetOpen i)) (sheetBiholomorph i) T).trans hLen)
    M hM hSTest
  choose e he using hPatches
  refine ⟨Z,R,hL,hRT,?_,?_,?_⟩
  · apply singular_stages_of_open_cover W sheetOpen hCover R
    intro i
    have h := singular_stages_of_tower_iso ((Subtype.val : sheetOpen i → sheetManifold) ⁻¹' W)
      (hClosed.preimage continuous_subtype_val) _ (he i)
    simpa only [Diffeomorph.coe_refl,preimage_id] using h (by
      simpa only [Diffeomorph.coe_refl,preimage_id] using hSStage i)
  · refine ⟨isClosed_closure,?_⟩
    intro z hz
    obtain ⟨i,hi⟩ := hCover (R.proj z)
    let WU := (Subtype.val : sheetOpen i → sheetManifold) ⁻¹' W
    have hEq := strictTransform_preimage_of_square
      (Diffeomorph.refl 𝓘c (CMfd.of (n := 3) (sheetOpen i)) ∞) (e i)
      (S i).tower.contMDiff_proj (restrict (sheetOpen i) R).contMDiff_proj WU
      (hClosed.preimage continuous_subtype_val) (fun y => ((he i).proj_comm y).symm)
    rw [Diffeomorph.coe_refl,preimage_id] at hEq
    have hS : IsClosedSubmanifold 3 (strictTransform 3 (restrict (sheetOpen i) R).proj WU) :=
      (isClosedSubmanifold_preimage_iff (e i)).mp (hEq ▸ hSSmooth i)
    let zU : openPreimage R (sheetOpen i) := ⟨z,hi⟩
    have hStrict := strictTransform_restricted_tower (sheetOpen i) R W
    have hzU : zU ∈ strictTransform 3 (restrict (sheetOpen i) R).proj WU := by
      rw [hStrict]
      exact hz
    obtain ⟨d,hd⟩ := hS.2 zU hzU
    rw [hStrict] at hd
    exact ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hd⟩
  · intro j hj
    ext x
    let u : sheetOpen x.1 := ⟨x,mem_singleton _,mem_univ _⟩
    have h := (slotFootprint_of_isTowerIso (he x.1) j).symm
    rw [Diffeomorph.coe_refl,preimage_id,slotFootprint_restrict,
      slotFootprint_of_isTowerIso (hIso x.1) j,hFoot j hj] at h
    exact Set.ext_iff.mp h u

#print axioms exists_whole_cusp_sheets_three_step_test

end
end Hironaka.HironakaG8SameClockCuspSheets
