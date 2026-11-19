import Hironaka.Resolution.HironakaG8RankedTestCompression

/-! Literal padding places a supplied three-stage sheet TEST on its prescribed clock. -/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ScheduledSheetTriple

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8RankedEmptyPadding HironakaG8RankOccupiedAnnotation HironakaG8RankedTestCompression
  HironakaSharpActualCurveEmptyPadding MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG3EmptyAwareHistory BlowupTowerIsomorphism

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem slotFootprint_eq_empty_of_length_le
    (T : BlowupTower X Y) {j : ℕ} (hj : T.length ≤ j) :
    slotFootprint T j = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (Nat.not_lt_of_ge hj) (occupied_lt_length T ((slotFootprint_nonempty_iff T j).mp ⟨x,hx⟩))

private theorem slotFootprint_append_identity
    (T : BlowupTower X Y) (k j : ℕ) :
    slotFootprint (T.append (identityEmptyTail Y k)) j = slotFootprint T j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (if j = (T.append (identityEmptyTail Y k)).length then
      (T.append (identityEmptyTail Y k)).proj '' (∅ : Set Y)
      else slotFootprint (T.append (identityEmptyTail Y k)) j) = _
    split
    · rename_i he
      have hle : T.length ≤ j := by
        rw [he,BlowupTower.length_append,identityEmptyTail_length]
        omega
      simp [slotFootprint_eq_empty_of_length_le T hle]
    · exact ih

private theorem assignedSlot_lt_clock {T : BlowupTower X Y} {N : ℕ} (D : RankedTower X T N)
    {j : ℕ} (hj : j < T.length) : assignedSlot D j < N := by
  induction D with
  | refl => exact (Nat.not_lt_zero _ hj).elim
  | @step A B S i k D hik C π hπ ih =>
    change (if j = S.length then k else assignedSlot D j) < k+1
    split
    · exact Nat.lt_succ_self _
    · rename_i hne
      have hlt : j < S.length := by change j < S.length+1 at hj; omega
      exact (ih hlt).trans (hik.trans_lt (Nat.lt_succ_self _))

/-- At each assigned raw clock, the padded tower has the original
projected footprint exactly. -/
theorem slotFootprint_ranked_through_assigned
    {T : BlowupTower X Y} {N : ℕ} (D : RankedTower X T N)
    (cap : ℕ) (j : Fin T.length) :
    slotFootprint (D.through cap) (assignedSlot D j.val) = slotFootprint T j.val := by
  change slotFootprint (D.pad.append (identityEmptyTail Y (cap-N))) (assignedSlot D j.val) = _
  rw [slotFootprint_append_identity]
  induction D with
  | refl => exact Fin.elim0 j
  | @step A B S i k D hik C π hπ ih =>
    let P :=  D.through k
    have hLen : P.length = k := D.through_length hik
    have hProj : P.proj = S.proj := D.through_proj k
    change (if (if j.val = S.length then k else assignedSlot D j.val) = P.length
      then P.proj '' C
      else slotFootprint P (if j.val = S.length then k else assignedSlot D j.val)) = _
    by_cases hj : j.val = S.length
    · rw [if_pos hj,hLen,if_pos rfl,hProj]
      simp [slotFootprint,hj]
    · have hlt : j.val < S.length := by
        have h := j.isLt
        change j.val < S.length+1 at h
        omega
      have hne : assignedSlot D j.val ≠ k := Nat.ne_of_lt ((assignedSlot_lt_clock D hlt).trans_le hik)
      rw [if_neg hj,hLen,if_neg hne]
      change slotFootprint (D.pad.append (identityEmptyTail A (k-i))) (assignedSlot D j.val) = _
      rw [slotFootprint_append_identity,ih ⟨j.val,hlt⟩]
      simp [slotFootprint,hj]

/-- Padding creates no additional occupied clock. -/
theorem exists_assignedSlot_of_nonempty_ranked_through
    {T : BlowupTower X Y} {N : ℕ} (D : RankedTower X T N) (cap j : ℕ)
    (hj : (slotFootprint (D.through cap) j).Nonempty) :
    ∃ p : Fin T.length, assignedSlot D p.val = j := by
  change (slotFootprint (D.pad.append (identityEmptyTail Y (cap-N))) j).Nonempty at hj
  rw [slotFootprint_append_identity] at hj
  induction D with
  | refl => exact (not_nonempty_empty hj).elim
  | @step A B S i k D hik C π hπ ih =>
    let P := D.through k
    have hLen : P.length = k := D.through_length hik
    by_cases he : j = k
    · refine ⟨⟨S.length,Nat.lt_succ_self _⟩,?_⟩
      change (if S.length = S.length then k else assignedSlot D S.length) = j
      simp [he]
    · change (if j = P.length then P.proj '' C else slotFootprint P j).Nonempty at hj
      rw [hLen,if_neg he] at hj
      change (slotFootprint (D.pad.append (identityEmptyTail A (k-i))) j).Nonempty at hj
      rw [slotFootprint_append_identity] at hj
      obtain ⟨q,hq⟩ := ih hj
      refine ⟨⟨q.val,Nat.lt_succ_of_lt q.isLt⟩,?_⟩
      change (if q.val = S.length then k else assignedSlot D q.val) = j
      rwa [if_neg (Nat.ne_of_lt q.isLt)]

private theorem emptyAware_append_identity
    {T S : BlowupTower X Y}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T S
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞)) (k : ℕ) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (T.append (identityEmptyTail Y k)) S (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hb := EmptyAwareTowerIso.leftEmpty ih BlowupExistenceCodimOne.isBlowupAlong_id_empty
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) (fun _ => rfl)
    simpa only [Diffeomorph.refl_trans,identityEmptyTail,BlowupTower.append_step] using hb

/-- The literal padding retains an actual empty-aware comparison whose
terminal map is the identity on the very same endpoint. -/
theorem ranked_through_emptyAware
    {T : BlowupTower X Y} {k : ℕ} (D : RankedTower X T k) (N : ℕ) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) (D.through N) T
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) := by
  apply emptyAware_append_identity _ (N-k)
  induction D with
  | refl => exact .refl
  | @step V W T i r D hi C π hπ ih =>
    exact .step (emptyAware_append_identity ih (r-i)) hπ hπ
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) W ∞) (fun _ => rfl) rfl

/-- The sheet s in chart 0 through m uses its first two clocks s and
s+1, and the terminal clock m+2. The tested padded tower has a common
length m+3 and preserves each of the three assigned raw footprints. -/
theorem exists_scheduled_sheet_triple
    (T : BlowupTower X Y) (hLen : T.length = 3)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hTest : IsGeoTestTower M T)
    (m s : ℕ) (hs : s ≤ m) :
    ∃ R : BlowupTower X Y, R.length = m+3 ∧ IsGeoTestTower M R ∧ R.proj = T.proj ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) R T
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) ∧
      slotFootprint R s = slotFootprint T 0 ∧
      slotFootprint R (s+1) = slotFootprint T 1 ∧
      slotFootprint R (m+2) = slotFootprint T 2 ∧
      (∀ j, (slotFootprint R j).Nonempty → j = s ∨ j = s+1 ∨ j = m+2) := by
  let rank (j : Fin T.length) := if j.val = 2 then m+2 else s+j.val
  have hStrict : StrictMono rank := by
    intro p q hpq
    have hp : p.val < 3 := p.isLt.trans_le hLen.le
    have hq : q.val < 3 := q.isLt.trans_le hLen.le
    change p.val < q.val at hpq
    unfold rank
    split <;> split <;> omega
  have hBound (j : Fin T.length) : rank j < m+3 := by
    have hj : j.val < 3 := j.isLt.trans_le hLen.le
    unfold rank
    split <;> omega
  obtain ⟨k,hk,D,hRank⟩ := exists_rankedTower_of_strictMono_slots T rank hStrict (m+3) hBound
  refine ⟨D.through (m+3),D.through_length hk,test_ranked_through M hM hTest D (m+3),
    D.through_proj _,ranked_through_emptyAware D _,?_,?_,?_,?_⟩
  · let j : Fin T.length := ⟨0,by omega⟩
    have h := slotFootprint_ranked_through_assigned D (m+3) j
    rw [hRank j] at h
    simpa [rank,j] using h
  · let j : Fin T.length := ⟨1,by omega⟩
    have h := slotFootprint_ranked_through_assigned D (m+3) j
    rw [hRank j] at h
    simpa [rank,j] using h
  · let j : Fin T.length := ⟨2,by omega⟩
    have h := slotFootprint_ranked_through_assigned D (m+3) j
    rw [hRank j] at h
    simpa [rank,j] using h

  · intro j hj
    obtain ⟨p,hp⟩ := exists_assignedSlot_of_nonempty_ranked_through D (m+3) j hj
    rw [hRank p] at hp
    have hpval : p.val < 3 := p.isLt.trans_le hLen.le
    unfold rank at hp
    split at hp <;> omega

end Hironaka.HironakaG8ScheduledSheetTriple
