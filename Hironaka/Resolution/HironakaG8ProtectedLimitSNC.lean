import Hironaka.Resolution.HironakaG8ProtectedStageLimitAtlas

/-! A protected chart carries the physical strict carrier and full ordered boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ProtectedLimitSNC
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryFactors
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryComparison
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaG8ProtectedStageLimitAtlas
  HironakaBaseChange HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSeparationChoiceComparison
  HironakaEmbeddedAnalytic HironakaActualLocallyFiniteBoundary
  HironakaSharpActualCurveBirthBoundaryOverlaps MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance MarkedIdealTowerTransport

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- The same protected atlas chart reads the differential strict transform
of the physical limit projection by open base change. The earlier history
can include boundary cleanup, since no singular-centre law is needed. -/
theorem protected_physical_strict_transform {n : ℕ} {X : CMfd.{0} n}
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)))
    (W : Set X) (hW : IsClosed W) :
    let e := protectedStageDiffeomorph s hLF U N hAvoid
    (Subtype.val : limitWindow s hLF U → limitManifold s hLF) ⁻¹'
        strictTransform n (gluedProjection s hLF) W =
      e ⁻¹' ((Subtype.val : openPreimage (s.stage N).2 U → (s.stage N).1) ⁻¹'
        strictTransform n (s.stage N).2.proj W) := by
  intro e
  let Y := limitManifold s hLF
  let P := (s.stage N).2
  let T := restrict U P
  let V := limitWindow s hLF U
  let f : V → U := T.proj ∘ e
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
    T.contMDiff_proj.comp e.contMDiff
  have square (z : V) : (gluedProjection s hLF : Y → X) z.val = (f z).val := by
    have h := protectedStageMap_projection s hLF U N z
    rw [← h]
    change P.proj (e z).val = (T.proj (e z)).val
    exact (proj_restrict U P (e z)).symm
  have hA := strictTransform_preimage_eq (gluedProjection_contMDiff s hLF) hf
    (isOpenHoloEmbedding_val U) (isOpenHoloEmbedding_val V) square W
  have hB := strictTransform_preimage_of_square
    (A' := CMfd.of (n := n) U) (A := CMfd.of (n := n) U)
    (B' := CMfd.of (n := n) V) (B := CMfd.of (n := n) (openPreimage P U))
    (π' := f) (π := T.proj)
    (Diffeomorph.refl (I := 𝓘(ℂ,ComplexModel n)) U ∞)
    e hf T.contMDiff_proj ((Subtype.val : U → X) ⁻¹' W)
    (hW.preimage continuous_subtype_val) (fun z => by change T.proj (e z) = f z; rfl)
  exact hA.symm.trans (hB.trans (by rw [strictTransform_restricted_tower]))

/-- A clean finite window gives a clean chart of the physical limit.
The finite visible boundary is the entire ordered prefix, including
any empty slots, and every later global slot has empty trace. -/
theorem protected_limit_snc_of_clean_stage {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hTest : ∀ j, IsGeoTestTower M (s.stage j).2) (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)))
    (W : Set X) (hW : IsClosed W) :
    let O := openPreimage (s.stage N).2 U
    let C := (Subtype.val : O → (s.stage N).1) ⁻¹' strictTransform n (s.stage N).2.proj W
    let E := (geoTransformAlong M (s.stage N).2).E.map ((Subtype.val : O → (s.stage N).1) ⁻¹' ·)
    IsClosedSubmanifold n C → IsSNCDivisor n E → HasNormalCrossings n C E → IsTransverse n C E →
    let V := limitWindow s hLF U
    let C' := (Subtype.val : V → limitManifold s hLF) ⁻¹' strictTransform n (gluedProjection s hLF) W
    let F := (List.range E.length).map (fun k =>
      (Subtype.val : V → limitManifold s hLF) ⁻¹' limitBoundaryMember M s hLF k)
    let e := protectedStageDiffeomorph s hLF U N hAvoid
    C' = e ⁻¹' C ∧ F = E.map (e ⁻¹' ·) ∧
    IsClosedSubmanifold n C' ∧ IsSNCDivisor n F ∧ HasNormalCrossings n C' F ∧ IsTransverse n C' F ∧
    ∀ k, E.length ≤ k →
      (Subtype.val : V → limitManifold s hLF) ⁻¹' limitBoundaryMember M s hLF k = ∅ := by
  intro O C E hC hE hNC hTrans V C' F e
  have hCarrier : C' = e ⁻¹' C := protected_physical_strict_transform s hLF U N hAvoid W hW
  have hBoundary : F = E.map (e ⁻¹' ·) := by
    apply List.ext_getElem (by simp [F])
    intro k hk hk'
    simp only [F,List.getElem_map,List.getElem_range]
    ext z
    have hb := protectedStageMap_boundary M hM s hLF hTest U N hAvoid k z
    have hkE : k < (geoTransformAlong M (s.stage N).2).E.length := by
      simpa only [F,List.length_map,List.length_range,E] using hk
    rw [boundaryReadout,List.getD_eq_getElem _ _ hkE] at hb
    change z.val ∈ limitBoundaryMember M s hLF k ↔ _ at hb
    simp only [E,List.getElem_map,mem_preimage]
    change z.val ∈ limitBoundaryMember M s hLF k ↔
      (protectedStageMap s hLF U N z).val ∈ (geoTransformAlong M (s.stage N).2).E[k]
    exact hb
  have hCoord : PullsBackCoordinates n (e : V → O) :=
    pullsBackCoordinates_of_forall_notMem_exceptionalLocus e.contMDiff
      (MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply)
  refine ⟨hCarrier,hBoundary,?_,?_,?_,?_,?_⟩
  · rw [hCarrier]
    exact (isClosedSubmanifold_preimage_iff e).mpr hC
  · rw [hBoundary]
    exact isSNCDivisor_map_preimage hCoord e.continuous hE
  · rw [hCarrier,hBoundary]
    exact hasNormalCrossings_preimage hCoord hNC
  · rw [hCarrier,hBoundary]
    exact isTransverse_preimage hCoord hTrans
  · intro k hk
    apply protectedStageMap_later_boundary_empty M hM s hLF hTest U N hAvoid
    simpa only [E,List.length_map,length_E_geoTransformAlong,stage_length] using hk

/-- Intrinsic singular continuation after a clean finite window supplies
the exact protection hypothesis of the limit atlas, even if the prior
finite history contains smooth boundary cleanup steps. -/
theorem clean_stage_protects_intrinsic_future {n : ℕ} {X : CMfd.{0} n}
    (s : GrowingSeq X) (U : Opens X) (N : ℕ)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    let O := openPreimage (s.stage N).2 U
    let V := strictTransform n (s.stage N).2.proj W
    IsClosedSubmanifold n ((Subtype.val : O → (s.stage N).1) ⁻¹' V) →
    (∀ r, HironakaStageCenters.StageCentres
      (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj V)) (tailTower s N r)) →
    ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)) := by
  intro O V hClean hFuture
  have hV := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW (s.stage N).2
  have hReg : Disjoint (singularSet (n := n) V) (O : Set (s.stage N).1) := by
    apply disjoint_left.mpr
    intro y hy hO
    let z : O := ⟨y,hO⟩
    obtain ⟨d,hd⟩ := hClean.2 z (mem_singularSet_iff.mp hy).1
    exact (mem_singularSet_iff.mp hy).2 d (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hd)
  apply protected_centres_of_empty_tails s U N
  intro r
  apply (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
  exact HironakaG8IntrinsicSingularBlockSchedule.intrinsic_singular_history_avoids_regular_open
    hV O hReg (tailTower s N r) (hFuture r)

#print axioms clean_stage_protects_intrinsic_future
#print axioms protected_limit_snc_of_clean_stage
#print axioms protected_physical_strict_transform

end
end Hironaka.HironakaG8ProtectedLimitSNC
