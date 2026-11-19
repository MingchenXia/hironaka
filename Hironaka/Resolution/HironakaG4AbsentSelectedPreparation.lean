import Hironaka.Resolution.HironakaG4SelectedPreparationHead
import Hironaka.Resolution.HironakaG4RetainedTraceComparison
import Hironaka.Resolution.HironakaG4RetainedCurrentStamp
import Hironaka.Resolution.HironakaG3AppendEmptyTailComparison

/-! A selected lower row absent from the source contributes only empty
centres, including those of its immediate actual distinct-defect rerun. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4AbsentSelectedPreparation

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4SharpTerminalAtlas
  HironakaG4RetainedPreparationTrace HironakaG4SelectedPreparationHead
  HironakaG4RetainedPreparationHeadTests HironakaG4RetainedTraceComparison
  HironakaG4ResidualInductionInputs HironakaG4RetainedLowerCompactWindow
  HironakaG4OrderedRetainedDefectTrace HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4RetainedCurrentStamp HironakaG4OrderedCrestEmptyBorn
  HironakaG3EmptyAwareHistory HironakaG3AppendEmptyTailComparison
  HironakaG8DisjointPhaseMerge HironakaG3EmptyAwareBornSlots
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem currentSharp_empty_carrier_isEmptyTower (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      CurrentSharpCentres (∅ : Set X) E T → IsEmptyTower T
  | _, .refl, _ => trivial
  | _, .step T C _ _, h => by
    refine ⟨currentSharp_empty_carrier_isEmptyTower E T h.1, subset_empty_iff.mp ?_⟩
    have hC := h.2
    rw [StepOneEmptyPrefix.strictAlong_empty T] at hC
    exact fun _ hx => (hC hx).1

private theorem retained_records_of_refl_comparison {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born) {T : BlowupTower X Y}
    {β : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      T (.refl : BlowupTower X X) β) :
    let A := geoTransformAlong (geometricTemplate N born) T
    A.N = β ⁻¹' N ∧ old.map (strictAlong T) = old.map (β ⁻¹' ·) ∧
      liveBorn A.E = (liveBorn born).map (β ⁻¹' ·) := by
  have hOld : old = old.map ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) ⁻¹' ·) :=
    (List.map_id old).symm
  have hBorn : liveBorn born = (liveBorn born).map ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) ⁻¹' ·) :=
    (List.map_id (liveBorn born)).symm
  obtain ⟨hNCur, hOldCur, hBornCur⟩ := retained_inputs_of_emptyAware
    (N' := N) (old' := old) (born' := born) g rfl hOld hBorn h
  change old.map (strictAlong T) = (old.map id).map (β ⁻¹' ·) at hOldCur
  rw [List.map_id] at hOldCur
  exact ⟨hNCur, hOldCur, hBornCur⟩

private theorem retained_noDefect_of_refl_comparison (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hNoDefect : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    {T : BlowupTower X Y}
    {β : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      T (.refl : BlowupTower X X) β) :
    let A := geoTransformAlong (geometricTemplate N born) T
    actualFamilyDistinctDefect A.N (oldResidualPart A.N (old.map (strictAlong T)) A.E) = ∅ := by
  intro A
  obtain ⟨hN,hOld,hBorn⟩ := retained_records_of_refl_comparison g h
  have hCurrent := (retainedDefect_and_rank_filter_empty_born A.N (old.map (strictAlong T)) A.E).1
  change actualFamilyDistinctDefect A.N
    (oldResidualPart A.N (old.map (strictAlong T)) (liveBorn A.E)) = _ at hCurrent
  rw [← hCurrent, hN, hOld, hBorn]
  have hPull := (actual_retained_defect_and_rank_biholomorph hn g.carrier g.full
    g.born_transverse g.dense β).1
  have hBornPull : liveBorn (born.map (β ⁻¹' ·)) = (liveBorn born).map (β ⁻¹' ·) :=
    filter_map_bijection β β.surjective born
  rw [← hBornPull]
  exact (retainedDefect_and_rank_filter_empty_born (β ⁻¹' N)
    (old.map (β ⁻¹' ·)) (born.map (β ⁻¹' ·))).1.trans
    (hPull.trans (hNoDefect ▸ preimage_empty))

set_option maxHeartbeats 850000 in
/-- If the selected native lower carrier is empty, the paired lower phase
and its actual defect rerun compare to the unchanged source. At that same
endpoint map the carrier, literal old list and nonempty born list all
read back to their inputs. -/
theorem absent_selected_preparation_prefix
    {hn : 0 < n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
    {i : ℕ} {later : List RetainedPreparationPhase}
    (H : SelectedPreparationHead hn N old born T i later)
    (hAbsent : N ∩ (oldResidualPart N old born H.row).zeroLocus = ∅) :
    let U := H.lower.append H.defect
    let A := geoTransformAlong (geometricTemplate N born) U
    ∃ β : H.defectTarget ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        U (.refl : BlowupTower X X) β ∧
      A.N = β ⁻¹' N ∧ old.map (strictAlong U) = old.map (β ⁻¹' ·) ∧
      liveBorn A.E = (liveBorn born).map (β ⁻¹' ·) := by
  intro U A
  have hSharp := H.terminal.sharp
  rw [hAbsent] at hSharp
  have hEmpty := currentSharp_empty_carrier_isEmptyTower _ H.lower hSharp
  obtain ⟨α, hα⟩ := emptyAware_append_empty_tail (.refl : BlowupTower X X) H.lower hEmpty
  rw [BlowupTower.refl_append] at hα
  have hNoDefect := retained_noDefect_of_refl_comparison hn H.geometry H.noDefect hα
  have gCurrent := H.lowerTests.current_geometry (hn := hn) H.geometry
  obtain ⟨χ,hχ⟩ :=
    compare_ordered_retained_traces gCurrent gCurrent rfl H.rerun (.done (μ := ⊤) hNoDefect)
  have hSameLower := emptyAware_of_isTowerIso (IsTowerIso.refl_self H.lower)
  have hAppend := emptyAware_append hSameLower hχ
  rw [BlowupTower.append_refl] at hAppend
  have hComparison : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      U (.refl : BlowupTower X X) (χ.trans α) := by
    simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hAppend hα
  exact ⟨χ.trans α,hComparison,retained_records_of_refl_comparison H.geometry hComparison⟩

/-- A selected literal empty old position has empty native lower carrier. -/
theorem selected_preparation_support_eq_empty_of_empty_old
    {hn : 0 < n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
    {i : ℕ} {later : List RetainedPreparationPhase}
    (H : SelectedPreparationHead hn N old born T i later)
    (hOld : old.get H.row = ∅) :
    N ∩ (oldResidualPart N old born H.row).zeroLocus = ∅ := by
  have g := H.geometry
  have hOrders := (retained_row_conditions_of_empty_distinct_defect hn g.carrier g.full
    g.born_transverse g.dense H.noDefect).1
  have hSub := (actual_residual_support_local_geometry hn g.carrier g.full
    g.born_transverse g.dense hOrders H.row).2.1
  exact subset_empty_iff.mp (hOld ▸ hSub)

end
end Hironaka.HironakaG4AbsentSelectedPreparation
