import Hironaka.Resolution.HironakaG4CertifiedSharpOuterComparison
import Hironaka.Resolution.HironakaG4CertifiedSharpFinishedRestriction
import Hironaka.Resolution.HironakaG4InitialRowScheduleAlignment
import Hironaka.Resolution.HironakaG4IncidenceLiveBoundaryComparison

/-! Compare the two actual blocks and close the recursive sharp chart comparison. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpFullComparison
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HomogenizedGlueingTower NormalCrossings
  HironakaG3EmptyAwareHistory HironakaG4CertifiedSharpHistory HironakaG4CertifiedSharpSourceView
  HironakaG4CertifiedSharpOuterComparison HironakaG4CertifiedSharpFinishedRestriction
  HironakaG4RetainedPreparationLowerHistory HironakaG4RetainedPreparationComparison
  HironakaG4RetainedPreparationEvent HironakaG4InitialRowScheduleAlignment
  HironakaG4IncidenceLiveBoundaryComparison

variable {n : ℕ} {hn : 0 < n} {lower : SharpHistoryPredicate.{u} n}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
/-- Compare the actual prepared prefixes, then their actual Γ continuations,
on the same literal source views. Each Γ cap is its own original length. -/
theorem finishedSharpOverlapCompatible_of_lower (actions : LowerHistoryActions lower)
    (compareLower : LowerHistoryOverlapCompatible lower) :
    FinishedSharpOverlapCompatible hn lower := by
  intro R' R U' U φ hCarrier hBoundary
  obtain ⟨B⟩ := finished_sharp_blocks_restrict R U
  obtain ⟨B'⟩ := finished_sharp_blocks_restrict R' U'
  let N := R.carrierOn U
  let E := R.boundaryOn U
  let N' := R'.carrierOn U'
  let E' := R'.boundaryOn U'
  let T := restrictedPreparedPrefix R U
  let T' := restrictedPreparedPrefix R' U'
  change N' = φ ⁻¹' N at hCarrier
  change HironakaG4RetainedTraceComparison.liveBorn E' =
    (HironakaG4RetainedTraceComparison.liveBorn E).map (φ ⁻¹' ·) at hBoundary
  have hAlign := sorted_original_retained_row_schedule_alignment φ hBoundary
  obtain ⟨ψ,hEq⟩ := compare_certified_retained_preparations actions compareLower φ
    (N := N) (N' := N') (old := E) (old' := E') (born := []) (born' := [])
    B.geometry B'.geometry hCarrier hBoundary rfl hAlign (T := T) (T' := T') B.preparation B'.preparation
      B.lower_histories B'.lower_histories
  have hFull : IsSNCDivisor n E := by simpa only [List.append_nil] using B.geometry.full
  have hFull' : IsSNCDivisor n E' := by simpa only [List.append_nil] using B'.geometry.full
  have hDense : N ⊆ closure (N \ ⋃ H ∈ E,H) := by simpa only [List.append_nil] using B.geometry.dense
  have hDense' : φ ⁻¹' N ⊆ closure (φ ⁻¹' N \ ⋃ H ∈ E',H) := by
    rw [←hCarrier]
    simpa only [List.append_nil] using B'.geometry.dense
  obtain ⟨χ,hΓ⟩ := incidence_processed_live_boundary_comparison hn (W := N) (E := E) (φ := φ) B.geometry.carrier hFull hDense
    E' hFull' hDense' hBoundary T T' hEq E.length E'.length le_rfl le_rfl B.suffix B'.suffix
    B.terminal.carrierTest B.terminal.boundaryTest
    (by simpa only [←hCarrier] using B'.terminal.carrierTest) B'.terminal.boundaryTest
    B.masks (by simpa only [←hCarrier] using B'.masks)
  have h := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso B'.physical.symm) hΓ)
    (emptyAware_of_isTowerIso B.physical)
  exact ⟨_,by simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using h⟩

/-- Independently chosen certified G4 charts compare over the supplied
biholomorphism after removal of their literally empty original slots. -/
theorem sharpHistory_overlap (hn : 0 < n) (d : ℕ) :
    LowerHistoryOverlapCompatible (SharpHistory.{u} hn d) := by
  refine sharpHistory_overlap_of_finished.{u} hn (fun j hLower => ?_) d
  exact finishedSharpOverlapCompatible_of_lower
    ⟨fun h U => sharpHistory_restrict h U,fun h e => sharpHistory_rebase hn j e _ h⟩ hLower

end
end Hironaka.HironakaG4CertifiedSharpFullComparison
