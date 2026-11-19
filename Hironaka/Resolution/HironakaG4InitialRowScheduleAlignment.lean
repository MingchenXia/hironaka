import Hironaka.Resolution.HironakaG4RetainedRowScheduleAlignment
import Hironaka.Resolution.HironakaG4SelectedLowerOverlapData

/-! Construct the original sorted row alignment from the equality of the
ordered nonempty old boundary. Empty slots retain their original indices. -/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.HironakaG4InitialRowScheduleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

open BlowupTowers HironakaG4RetainedTraceComparison
  HironakaG4RetainedRowScheduleAlignment HironakaG4SelectedLowerOverlapData

private theorem live_count_take_succ {A : Type u} (l : List (Set A)) {i : ℕ}
    (hi : i < l.length) :
    (liveBorn (l.take (i + 1))).length =
      (liveBorn (l.take i)).length + if l[i].Nonempty then 1 else 0 := by
  have hSingle : (liveBorn [l[i]]).length = (if l[i].Nonempty then 1 else 0) := by
    by_cases h : l[i].Nonempty <;> simp [liveBorn, h]
  rw [List.take_succ_eq_append_getElem hi, ← hSingle]
  simp only [liveBorn, List.filter_append, List.length_append]

private theorem live_count_take_lt_of_live {A : Type u} (l : List (Set A)) {i : ℕ}
    (hi : i < l.length) (h : l[i].Nonempty) :
    (liveBorn (l.take i)).length < (liveBorn l).length := by
  have hGrow := live_count_take_succ l hi
  rw [if_pos h] at hGrow
  have hTotal := congrArg (fun a : List (Set A) => (liveBorn a).length)
    (List.take_append_drop (i + 1) l)
  change (liveBorn (l.take (i + 1) ++ l.drop (i + 1))).length = _ at hTotal
  unfold liveBorn at hTotal hGrow ⊢
  rw [List.filter_append, List.length_append] at hTotal
  omega

private theorem range'_of_lt {i n : ℕ} (hi : i < n) :
    List.range' i (n - i) = i :: List.range' (i + 1) (n - (i + 1)) := by
  conv_lhs => rw [show n - i = n - (i + 1) + 1 by omega]
  rw [List.range'_succ]

private theorem align_from {n : ℕ} {X X' : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (old' : List (Set X')) (old : List (Set X))
    (hOld : liveBorn old' = (liveBorn old).map (e ⁻¹' ·))
    (i' i : ℕ) (hLe' : i' ≤ old'.length) (hLe : i ≤ old.length)
    (hPos : (liveBorn (old'.take i')).length = (liveBorn (old.take i)).length) :
    RetainedRowScheduleAlignment e old' old
      (List.range' i' (old'.length - i')) (List.range' i (old.length - i)) := by
  have hTotal := congrArg List.length hOld
  rw [List.length_map] at hTotal
  by_cases hIndex' : i' < old'.length
  · rw [range'_of_lt hIndex']
    by_cases hLive' : old'[i'].Nonempty
    · by_cases hIndex : i < old.length
      · rw [range'_of_lt hIndex]
        by_cases hLive : old[i].Nonempty
        · obtain ⟨hRow, hErase⟩ := matched_old_rows_of_live_positions e hOld
            ⟨i, hIndex⟩ ⟨i', hIndex'⟩ hLive hLive' hPos
          have hRowOpt : old'[i']? = (old[i]?).map (e ⁻¹' ·) := by
            rw [List.getElem?_eq_getElem hIndex', List.getElem?_eq_getElem hIndex, Option.map_some]
            exact congrArg some hRow
          have hNext : (liveBorn (old'.take (i' + 1))).length =
              (liveBorn (old.take (i + 1))).length := by
            rw [live_count_take_succ old' hIndex', live_count_take_succ old hIndex,
              if_pos hLive', if_pos hLive, hPos]
          exact .pair hRowOpt hErase (align_from e old' old hOld (i' + 1) (i + 1)
            (by omega) (by omega) hNext)
        · have hEmpty : old[i]? = some ∅ := by
            rw [List.getElem?_eq_getElem hIndex, not_nonempty_iff_eq_empty.mp hLive]
          have hNext : (liveBorn (old'.take i')).length =
              (liveBorn (old.take (i + 1))).length := by
            rw [live_count_take_succ old hIndex, if_neg hLive, Nat.add_zero, hPos]
          have hRest := align_from e old' old hOld i' (i + 1) hLe' (by omega) hNext
          rw [range'_of_lt hIndex'] at hRest
          exact .rightEmpty hEmpty hRest
      · have hPrefix : (liveBorn (old.take i)).length = (liveBorn old).length := by
          rw [List.take_of_length_le (by omega : old.length ≤ i)]
        have hLt := live_count_take_lt_of_live old' hIndex' hLive'
        omega
    · have hEmpty' : old'[i']? = some ∅ := by
        rw [List.getElem?_eq_getElem hIndex', not_nonempty_iff_eq_empty.mp hLive']
      have hNext : (liveBorn (old'.take (i' + 1))).length =
          (liveBorn (old.take i)).length := by
        rw [live_count_take_succ old' hIndex', if_neg hLive', Nat.add_zero, hPos]
      exact .leftEmpty hEmpty' (align_from e old' old hOld (i' + 1) i (by omega) hLe hNext)
  · have hStop' : old'.length - i' = 0 := by omega
    rw [hStop', List.range'_zero]
    by_cases hIndex : i < old.length
    · rw [range'_of_lt hIndex]
      have hEmptyRow : ¬ old[i].Nonempty := by
        intro hLive
        have hPrefix' : (liveBorn (old'.take i')).length = (liveBorn old').length := by
          rw [List.take_of_length_le (by omega : old'.length ≤ i')]
        have hLt := live_count_take_lt_of_live old hIndex hLive
        omega
      have hEmpty : old[i]? = some ∅ := by
        rw [List.getElem?_eq_getElem hIndex, not_nonempty_iff_eq_empty.mp hEmptyRow]
      have hNext : (liveBorn (old'.take i')).length =
          (liveBorn (old.take (i + 1))).length := by
        rw [live_count_take_succ old hIndex, if_neg hEmptyRow, Nat.add_zero, hPos]
      have hRest := align_from e old' old hOld i' (i + 1) hLe' (by omega) hNext
      rw [hStop', List.range'_zero] at hRest
      exact .rightEmpty hEmpty hRest
    · have hStop : old.length - i = 0 := by omega
      rw [hStop, List.range'_zero]
      exact .done
termination_by (old'.length - i') + (old.length - i)
decreasing_by all_goals omega

/-- Equality of the ordered nonempty old lists aligns all original row
positions in increasing order. An unmatched position is literally empty. -/
theorem initial_retained_row_schedule_alignment {n : ℕ} {X X' : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {old' : List (Set X')} {old : List (Set X)}
    (hOld : liveBorn old' = (liveBorn old).map (e ⁻¹' ·)) :
    RetainedRowScheduleAlignment e old' old (List.range old'.length) (List.range old.length) := by
  simpa only [List.range_eq_range', Nat.sub_zero] using
    (align_from e old' old hOld 0 0 (Nat.zero_le _) (Nat.zero_le _) (by simp [liveBorn]))

/-- The increasing full schedule used by the retained preparation fold has
the original natural-number row labels. -/
theorem sorted_original_row_indices (k : ℕ) :
    (((Finset.univ : Finset (Fin k)).sort (· ≤ ·)).map Fin.val) = List.range k := by
  rw [Fin.sort_univ]
  apply List.ext_getElem
  · simp
  · intros
    simp

/-- Align the exact index lists of the full sorted retained preparations. -/
theorem sorted_original_retained_row_schedule_alignment {n : ℕ} {X X' : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {old' : List (Set X')} {old : List (Set X)}
    (hOld : liveBorn old' = (liveBorn old).map (e ⁻¹' ·)) :
    RetainedRowScheduleAlignment e old' old
      (((Finset.univ : Finset (Fin old'.length)).sort (· ≤ ·)).map Fin.val)
      (((Finset.univ : Finset (Fin old.length)).sort (· ≤ ·)).map Fin.val) := by
  simpa only [sorted_original_row_indices] using initial_retained_row_schedule_alignment e hOld

end
end Hironaka.HironakaG4InitialRowScheduleAlignment
