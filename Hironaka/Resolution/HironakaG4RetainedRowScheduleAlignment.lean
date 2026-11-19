import Hironaka.Resolution.HironakaG4RetainedTraceComparison
import Hironaka.Invariant.StepOneEmptyPrefix

/-! Pair the retained old positions of two actual preparation schedules
before comparing their blocks. The pairing survives a physical prefix
comparison, even when matched rows subsequently become empty. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4RetainedRowScheduleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HomogenizedGlueingTower HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareOldSlots HironakaG3EmptyAwareFilteredBoundary
  HironakaG3EmptyAwareFullBoundary HironakaG3EmptyAwareBornSlots
  HironakaG4RetainedTraceComparison HironakaG4OrderedRetainedDefectTrace
  NormalCrossings NormalCrossingsComparison HironakaSharpActualFiniteChronologicalHistory

/-- Paired selected rows have matching actual old slots and matching
filtered old lists after removing those positions. An unpaired row is a
literal empty slot. The indices keep their original numerical labels. -/
inductive RetainedRowScheduleAlignment {X X' : Type u} (f : X' → X)
    (old' : List (Set X')) (old : List (Set X)) : List ℕ → List ℕ → Prop
  | done : RetainedRowScheduleAlignment f old' old [] []
  | pair {j' j : ℕ} {rest' rest : List ℕ}
      (row : old'[j']? = (old[j]?).map (f ⁻¹' ·))
      (remaining : liveBorn (old'.eraseIdx j') = (liveBorn (old.eraseIdx j)).map (f ⁻¹' ·))
      (tail : RetainedRowScheduleAlignment f old' old rest' rest) :
      RetainedRowScheduleAlignment f old' old (j' :: rest') (j :: rest)
  | leftEmpty {j' : ℕ} {rest' rest : List ℕ}
      (empty : old'[j']? = some ∅)
      (tail : RetainedRowScheduleAlignment f old' old rest' rest) :
      RetainedRowScheduleAlignment f old' old (j' :: rest') rest
  | rightEmpty {j : ℕ} {rest' rest : List ℕ}
      (empty : old[j]? = some ∅)
      (tail : RetainedRowScheduleAlignment f old' old rest' rest) :
      RetainedRowScheduleAlignment f old' old rest' (j :: rest)

variable {n : ℕ} {X X' A A' : CMfd.{u} n}

private theorem filtered_old_after_prefix
    {old' : List (Set X')} {old : List (Set X)} (hClosed : ∀ H ∈ old, IsClosed H)
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    {P' : BlowupTower X' A'} {P : BlowupTower X A}
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    (hP : EmptyAwareTowerIso φ P' P β) :
    liveBorn (old'.map (strictAlong P')) =
      (liveBorn (old.map (strictAlong P))).map (β ⁻¹' ·) := by
  have h : liveBorn old' = liveBorn (old.map (φ ⁻¹' ·)) := by
    unfold liveBorn at *
    rwa [filter_map_bijection φ φ.surjective]
  have hFull := full_boundary_transport_of_filtered_initial hP
    (geometricTemplate (Set.univ : Set X') old') (geometricTemplate (Set.univ : Set X) old) h hClosed
  simp only [boundary_decomp, List.filter_append, List.map_append, emptyAware_born_boundary hP] at hFull
  exact List.append_cancel_right hFull

/-- All remaining paired and empty slots preserve their evidence under the
same actual prefix comparison. No row is dropped when a strict transform
of a matched pair becomes empty. -/
theorem RetainedRowScheduleAlignment.of_emptyAware
    {old' : List (Set X')} {old : List (Set X)} {indices' indices : List ℕ}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (align : RetainedRowScheduleAlignment φ old' old indices' indices)
    (hClosed : ∀ H ∈ old, IsClosed H)
    {P' : BlowupTower X' A'} {P : BlowupTower X A}
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    (hP : EmptyAwareTowerIso φ P' P β) :
    RetainedRowScheduleAlignment β (old'.map (strictAlong P')) (old.map (strictAlong P)) indices' indices := by
  induction align with
  | done => exact .done
  | @pair j' j tail' tail hRow hRest align ih =>
    refine .pair ?_ ?_ ih
    · rw [List.getElem?_map, List.getElem?_map, hRow]
      cases h : old[j]? with
      | none => rfl
      | some H =>
        exact congrArg some (emptyAware_strictAlong_eq hP H (hClosed H (List.mem_of_getElem? h)))
    · rw [List.eraseIdx_map, List.eraseIdx_map]
      exact filtered_old_after_prefix (fun H hH => hClosed H ((List.eraseIdx_sublist old j).subset hH))
        hRest hP
  | leftEmpty hEmpty _ ih =>
    exact .leftEmpty (by rw [List.getElem?_map, hEmpty]; simp [StepOneEmptyPrefix.strictAlong_empty]) ih
  | rightEmpty hEmpty _ ih =>
    exact .rightEmpty (by rw [List.getElem?_map, hEmpty]; simp [StepOneEmptyPrefix.strictAlong_empty]) ih

end
end Hironaka.HironakaG4RetainedRowScheduleAlignment
