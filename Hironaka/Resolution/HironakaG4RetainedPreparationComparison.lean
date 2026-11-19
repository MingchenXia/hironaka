import Hironaka.Resolution.HironakaG4RetainedRowScheduleAlignment
import Hironaka.Resolution.HironakaG4AbsentSelectedPreparation
import Hironaka.Resolution.HironakaG4SelectedRetainedRowOverlap

/-! Compare the actual preparation towers by the retained row schedule.
The lower leaves are compared by their supplied smaller history class. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4RetainedPreparationComparison

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsComparison
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareBornSlots HironakaG8DisjointPhaseMerge
  HironakaSharpActualFiniteChronologicalHistory HironakaG4RetainedTraceComparison
  HironakaG4OrderedRetainedDefectTrace HironakaG4RetainedPreparationTrace
  HironakaG4RetainedPreparationEvent HironakaG4RetainedPreparationHead
  HironakaG4RetainedPreparationHeadTests HironakaG4SelectedPreparationHead
  HironakaG4RetainedPreparationLowerHistory HironakaG4RetainedRowScheduleAlignment
  HironakaG4AbsentSelectedPreparation HironakaG4SelectedRetainedRowOverlap
  HironakaG4ResidualInductionInputs HironakaG4RetainedLowerCompactWindow
  HironakaG4PreparedCentreCoordinates

variable {n : ℕ}

/-- Physical comparison in the smaller-dimensional history class, at the
actual selected carrier and the same ordered nonempty lower boundary. -/
def LowerHistoryOverlapCompatible (P : SharpHistoryPredicate.{u} n) : Prop :=
  ∀ {X X' Y Y' : CMfd.{u} n} (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'},
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    IsClosedSubmanifold n W' → IsSNCDivisor n E' → W' ⊆ closure (W' \ ⋃ H ∈ E',H) →
    W' = φ ⁻¹' W → liveBorn E' = (liveBorn E).map (φ ⁻¹' ·) →
    P W E T → P W' E' T' →
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ

private theorem selected_lower_geometry
    {X Y : CMfd.{u} n} {hn : 0 < n} {N : Set X} {old born : List (Set X)}
    {T : BlowupTower X Y} {i : ℕ} {later : List RetainedPreparationPhase}
    (H : SelectedPreparationHead hn N old born T i later) :
    let L := N ∩ (oldResidualPart N old born H.row).zeroLocus
    let E := remainingBoundary old born H.row
    IsClosedSubmanifold n L ∧ IsSNCDivisor n E ∧ L ⊆ closure (L \ ⋃ D ∈ E,D) := by
  have g := H.geometry
  obtain ⟨orders, distinct⟩ := retained_row_conditions_of_empty_distinct_defect hn
    g.carrier g.full g.born_transverse g.dense H.noDefect
  refine ⟨(actual_residual_support_local_geometry hn g.carrier g.full
    g.born_transverse g.dense orders H.row).1, ?_, ?_⟩
  · exact isSNCDivisor_of_sublist g.full
      ((List.eraseIdx_sublist old H.row.val).append_right born)
  · exact residual_support_dense_off_remainingBoundary_of_local_dimension hn
      g.carrier g.full g.born_transverse g.dense orders distinct H.row

private theorem prefix_tests {X Y : CMfd.{u} n} {hn : 0 < n}
    {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y} {i : ℕ} {later : List RetainedPreparationPhase}
    (H : SelectedPreparationHead hn N old born T i later) :
    BlockTests N old born (H.lower.append H.defect) :=
  (blockTests_append_iff H.lower H.defect).mpr ⟨H.lowerTests, ordered_defect_blockTests H.rerun⟩

private theorem append_comparison {X X' A A' Y Y' Z Z' : CMfd.{u} n}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {Q : BlowupTower X A} {Q' : BlowupTower X' A'}
    {S : BlowupTower A Z} {S' : BlowupTower A' Z'}
    {e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    {e' : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z'}
    (h : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T (Q.append S) e)
    (h' : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X' ∞) T' (Q'.append S') e')
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hQ : EmptyAwareTowerIso φ Q' Q β) (hS : EmptyAwareTowerIso β S' S χ) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T η := by
  refine ⟨(e'.trans χ).trans e.symm, ?_⟩
  have same := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso h') (emptyAware_append hQ hS))
    (emptyAware_of_isTowerIso h.symm)
  simpa only [Diffeomorph.refl_trans,Diffeomorph.symm_refl,Diffeomorph.trans_refl] using same

private theorem compare_paired_prefix {X X' Y Y' : CMfd.{u} n} {hn : 0 < n}
    {P : SharpHistoryPredicate.{u} n} (compareLower : LowerHistoryOverlapCompatible P)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {N' : Set X'} {old born : List (Set X)} {old' born' : List (Set X')}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {i i' : ℕ} {phases phases' : List RetainedPreparationPhase}
    (H : SelectedPreparationHead hn N old born T i phases)
    (H' : SelectedPreparationHead hn N' old' born' T' i' phases')
    (c : H.usesLowerHistory P) (c' : H'.usesLowerHistory P)
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    (hRow : old'[i']? = (old[i]?).map (φ ⁻¹' ·))
    (hRest : liveBorn (old'.eraseIdx i') = (liveBorn (old.eraseIdx i)).map (φ ⁻¹' ·)) :
    ∃ β : H'.defectTarget ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ H.defectTarget,
      EmptyAwareTowerIso φ (H'.lower.append H'.defect) (H.lower.append H.defect) β := by
  have hRow' : old'.get H'.row = φ ⁻¹' old.get H.row := by
    rw [← H'.rowIndex, ← H.rowIndex, List.getElem?_eq_getElem H'.row.isLt,
      List.getElem?_eq_getElem H.row.isLt, Option.map_some, Option.some.injEq] at hRow
    exact hRow
  have hRest' : liveBorn (old'.eraseIdx H'.row.val) =
      (liveBorn (old.eraseIdx H.row.val)).map (φ ⁻¹' ·) := by
    simpa only [H'.rowIndex,H.rowIndex] using hRest
  obtain ⟨hW, hE, hD⟩ := selected_lower_geometry H
  obtain ⟨hW', hE', hD'⟩ := selected_lower_geometry H'
  exact compare_matched_retained_row_and_preparation hn φ H.geometry H'.geometry hN hOld hBorn
    H.row H'.row hRow' hRest'
    (fun hL hF => compareLower φ hW hE hD hW' hE' hD' hL hF c.1 c'.1)
    H.lowerTests.carrier H.lowerTests.full H'.lowerTests.carrier H'.lowerTests.full H.rerun H'.rerun

private abbrev rowPhases (indices : List ℕ) : List RetainedPreparationPhase :=
  indices.flatMap (fun i => [.lower i,.defect])

private theorem preparation_nonempty {X Y : CMfd.{u} n} {hn : 0 < n}
    {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
    {phases : List RetainedPreparationPhase}
    (tape : RetainedPreparationTrace hn N old born phases T) : phases ≠ [] := by
  induction tape with
  | lower => simp
  | defect => simp
  | append _ _ _ _ _ _ _ h₁ _ => simp [h₁]
  | restrictOpen _ _ _ ih => exact ih
  | rebase _ _ _ ih => exact ih

private def tailSelectedHead {X Y : CMfd.{u} n} {hn : 0 < n}
    {P : SharpHistoryPredicate.{u} n} (actions : LowerHistoryActions P)
    {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y} {i : ℕ} {later : List ℕ}
    (tail : RetainedPreparationTail hn N old born (rowPhases (i :: later)) T)
    (h : tail.usesLowerHistory P) :
    {H : SelectedPreparationHead hn N old born T i (rowPhases later) // H.usesLowerHistory P} := by
  change RetainedPreparationTail hn N old born (.lower i :: .defect :: rowPhases later) T at tail
  cases tail with
  | trace tape => exact selectedPreparationHeadWithLower actions tape h

private def CompareRowsBelow (hn : 0 < n) (P : SharpHistoryPredicate.{u} n) (k : ℕ) : Prop :=
  ∀ {X X' Y Y' : CMfd.{u} n} (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {N' : Set X'} {old born : List (Set X)} {old' born' : List (Set X')},
    NativeRetainedGeometry N old born → NativeRetainedGeometry N' old' born' →
    N' = φ ⁻¹' N → liveBorn old' = (liveBorn old).map (φ ⁻¹' ·) →
    liveBorn born' = (liveBorn born).map (φ ⁻¹' ·) →
    ∀ {indices' indices : List ℕ}, RetainedRowScheduleAlignment φ old' old indices' indices →
    ∀ {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    (S : RetainedPreparationTail hn N old born (rowPhases indices) T)
    (S' : RetainedPreparationTail hn N' old' born' (rowPhases indices') T'),
    S.usesLowerHistory P → S'.usesLowerHistory P → indices'.length + indices.length < k →
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ

private theorem compare_continuations {hn : 0 < n} {P : SharpHistoryPredicate.{u} n} {k : ℕ}
    (ih : CompareRowsBelow hn P k)
    {X X' A A' Y Y' : CMfd.{u} n} {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {N : Set X} {N' : Set X'} {old born : List (Set X)} {old' born' : List (Set X')}
    (g : NativeRetainedGeometry N old born) (g' : NativeRetainedGeometry N' old' born')
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {indices' indices : List ℕ} (align : RetainedRowScheduleAlignment φ old' old indices' indices)
    {Q : BlowupTower X A} {Q' : BlowupTower X' A'}
    (tests : BlockTests N old born Q) (tests' : BlockTests N' old' born' Q')
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A} (hQ : EmptyAwareTowerIso φ Q' Q β)
    {T : BlowupTower A Y} {T' : BlowupTower A' Y'}
    (S : let C := geoTransformAlong (geometricTemplate N born) Q
      RetainedPreparationTail hn C.N (old.map (strictAlong Q)) C.E (rowPhases indices) T)
    (S' : let C' := geoTransformAlong (geometricTemplate N' born') Q'
      RetainedPreparationTail hn C'.N (old'.map (strictAlong Q')) C'.E (rowPhases indices') T')
    (c : S.usesLowerHistory P) (c' : S'.usesLowerHistory P)
    (hCount : indices'.length + indices.length < k) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso β T' T χ := by
  obtain ⟨cN, cOld, cBorn⟩ := retained_filtered_inputs_of_emptyAware g hN hOld hBorn hQ
  have alignNext := align.of_emptyAware (fun H h => g.full.1 H (List.mem_append_left _ h)) hQ
  exact ih β (tests.current_geometry (hn := hn) g) (tests'.current_geometry (hn := hn) g')
    cN cOld cBorn alignNext S S' c c' hCount

private theorem reflexive_continuation {hn : 0 < n} {P : SharpHistoryPredicate.{u} n}
    {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
    {phases : List RetainedPreparationPhase} (S : RetainedPreparationTail hn N old born phases T)
    (c : S.usesLowerHistory P) :
    let Q : BlowupTower X X := .refl
    let C := geoTransformAlong (geometricTemplate N born) Q
    ∃ S' : RetainedPreparationTail hn C.N (old.map (strictAlong Q)) C.E phases T,
      S'.usesLowerHistory P := by
  change ∃ S' : RetainedPreparationTail hn N (old.map id) born phases T, S'.usesLowerHistory P
  rw [List.map_id]
  exact ⟨S,c⟩

private theorem old_row_empty_of_missing_label {X Y : CMfd.{u} n} {hn : 0 < n}
    {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y} {i : ℕ} {later : List RetainedPreparationPhase}
    (H : SelectedPreparationHead hn N old born T i later) (h : old[i]? = some ∅) :
    N ∩ (oldResidualPart N old born H.row).zeroLocus = ∅ := by
  rw [← H.rowIndex, List.getElem?_eq_getElem H.row.isLt, Option.some.injEq] at h
  exact selected_preparation_support_eq_empty_of_empty_old H h

set_option maxHeartbeats 1350000 in
private theorem compare_rows_below {hn : 0 < n} {P : SharpHistoryPredicate.{u} n}
    (actions : LowerHistoryActions P) (compareLower : LowerHistoryOverlapCompatible P) :
    ∀ k, CompareRowsBelow hn P k := by
  intro k
  induction k with
  | zero =>
      intro X X' Y Y' φ N N' old born old' born' g g' hN hOld hBorn indices' indices align T T' S S' c c' hCount
      exact (Nat.not_lt_zero _ hCount).elim
  | succ k ih =>
      intro X X' Y Y' φ N N' old born old' born' g g' hN hOld hBorn indices' indices align T T' S S' c c' hCount
      cases align with
      | done =>
          cases S with
          | trace tape => exact (preparation_nonempty tape rfl).elim
          | nil =>
              cases S' with
              | trace tape => exact (preparation_nonempty tape rfl).elim
              | nil => exact ⟨φ,.refl⟩
      | pair hRow hRest align =>
          obtain ⟨H,hH⟩ := tailSelectedHead actions S c
          obtain ⟨H',hH'⟩ := tailSelectedHead actions S' c'
          obtain ⟨β,hβ⟩ := compare_paired_prefix compareLower φ H H' hH hH' hN hOld hBorn hRow hRest
          obtain ⟨χ,hχ⟩ := compare_continuations ih g g' hN hOld hBorn align
            (prefix_tests H) (prefix_tests H') hβ H.continuation H'.continuation hH.2 hH'.2 (by simp only [List.length_cons] at hCount; omega)
          exact append_comparison H.iso H'.iso hβ hχ
      | leftEmpty hMissing align =>
          obtain ⟨H',hH'⟩ := tailSelectedHead actions S' c'
          obtain ⟨α,hα,_,_,_⟩ := absent_selected_preparation_prefix H' (old_row_empty_of_missing_label H' hMissing)
          have hβ := G3UniverseEmptyAwareCore.trans hα (EmptyAwareTowerIso.refl (Φ := φ))
          obtain ⟨reflS,reflC⟩ := reflexive_continuation S c
          obtain ⟨χ,hχ⟩ := compare_continuations ih g g' hN hOld hBorn align
            (⟨trivial,trivial⟩ : BlockTests N old born (.refl : BlowupTower X X)) (prefix_tests H')
            (by simpa only [Diffeomorph.refl_trans] using hβ)
            reflS H'.continuation reflC hH'.2 (by simp only [List.length_cons] at hCount; omega)
          have hI : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
              T ((.refl : BlowupTower X X).append T) (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) := by
            simpa only [BlowupTower.refl_append] using IsTowerIso.refl_self T
          exact append_comparison hI H'.iso (by simpa only [Diffeomorph.refl_trans] using hβ) hχ
      | rightEmpty hMissing align =>
          obtain ⟨H,hH⟩ := tailSelectedHead actions S c
          obtain ⟨α,hα,_,_,_⟩ := absent_selected_preparation_prefix H (old_row_empty_of_missing_label H hMissing)
          have hβ := G3UniverseEmptyAwareCore.trans (EmptyAwareTowerIso.refl (Φ := φ))
            (G3UniverseEmptyAwareCore.symm hα)
          obtain ⟨reflS,reflC⟩ := reflexive_continuation S' c'
          obtain ⟨χ,hχ⟩ := compare_continuations ih g g' hN hOld hBorn align
            (prefix_tests H) (⟨trivial,trivial⟩ : BlockTests N' old' born' (.refl : BlowupTower X' X'))
            (by simpa only [Diffeomorph.symm_refl,Diffeomorph.trans_refl] using hβ)
            H.continuation reflS hH.2 reflC (by simp only [List.length_cons] at hCount; omega)
          have hI : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X' ∞)
              T' ((.refl : BlowupTower X' X').append T') (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y' ∞) := by
            simpa only [BlowupTower.refl_append] using IsTowerIso.refl_self T'
          exact append_comparison H.iso hI
            (by simpa only [Diffeomorph.symm_refl,Diffeomorph.trans_refl] using hβ) hχ

/-- Compare the full actual preparation histories. The index alignment
permits extra empty old slots and retains every selected lower certificate. -/
theorem compare_certified_retained_preparations {hn : 0 < n} {P : SharpHistoryPredicate.{u} n}
    (actions : LowerHistoryActions P) (compareLower : LowerHistoryOverlapCompatible P)
    {X X' Y Y' : CMfd.{u} n} (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {N' : Set X'} {old born : List (Set X)} {old' born' : List (Set X')}
    (g : NativeRetainedGeometry N old born) (g' : NativeRetainedGeometry N' old' born')
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {indices' indices : List ℕ} (align : RetainedRowScheduleAlignment φ old' old indices' indices)
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    (S : RetainedPreparationTrace hn N old born (retainedPreparationPhases indices) T)
    (S' : RetainedPreparationTrace hn N' old' born' (retainedPreparationPhases indices') T')
    (c : usesLowerHistory P S) (c' : usesLowerHistory P S') :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ := by
  obtain ⟨head, cert⟩ := retainedPreparationHeadWithLower actions S c
  obtain ⟨head', cert'⟩ := retainedPreparationHeadWithLower actions S' c'
  cases head with
  | cons Q R event tail e hI =>
      cases event with
      | defect D =>
          cases head' with
          | cons Q' R' event' tail' e' hI' =>
              cases event' with
              | defect D' =>
                  obtain ⟨β,hβ⟩ :=
                    compare_aligned_filtered_ordered_retained_traces g g' φ hN hOld hBorn D' D
                  obtain ⟨χ,hχ⟩ := compare_continuations
                    (compare_rows_below actions compareLower (indices'.length + indices.length + 1))
                    g g' hN hOld hBorn align (ordered_defect_blockTests D) (ordered_defect_blockTests D')
                    hβ tail tail' cert.2 cert'.2 (Nat.lt_succ_self _)
                  exact append_comparison hI hI' hβ hχ

end
end Hironaka.HironakaG4RetainedPreparationComparison
