import Hironaka.Resolution.HironakaG4MaskScheduleEmptyRow

/-! Repeated insertion of absent rows and exact projection of its labels. -/

set_option autoImplicit false

namespace Hironaka.HironakaG4MaskScheduleEmptyRows

noncomputable section

open HironakaG4MaskScheduleEmptyRow HironakaG4ProcessedMaskIncidenceOrder
  HironakaG4RelativeOrderedProcessedFinish

/-- The chronological old-row embedding obtained by repeatedly inserting
one slot at a literal position. -/
inductive OldRowInsertion (r : ℕ) : (s : ℕ) → (Fin r ↪ Fin s) → Type
  | refl : OldRowInsertion r r (Function.Embedding.refl _)
  | insert {s : ℕ} {e : Fin r ↪ Fin s}
      (p : OldRowInsertion r s e) (j : Fin (s+1)) :
      OldRowInsertion r (s+1) (e.trans j.succAboveEmb)

namespace OldRowInsertion

variable {r s : ℕ} {e : Fin r ↪ Fin s}

/-- Every order-preserving embedding of the old positions is a finite
sequence of literal insertions. -/
theorem of_strictMono {e : Fin r ↪ Fin s} (hMono : StrictMono e) :
    Nonempty (OldRowInsertion r s e) := by
  classical
  induction s with
  | zero =>
    have hr : r ≤ 0 := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
    obtain rfl : r = 0 := Nat.le_zero.mp hr
    have he : e = Function.Embedding.refl _ := by
      ext i
      exact Fin.elim0 i
    rw [he]
    exact ⟨.refl⟩
  | succ s ih =>
    by_cases hSurj : Function.Surjective e
    · have hLen : r = s+1 := by
        simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective e ⟨e.injective,hSurj⟩)
      subst r
      have he : e = Function.Embedding.refl _ := Function.Embedding.ext fun i => congrFun hMono.eq_id i
      rw [he]
      exact ⟨.refl⟩
    · simp only [Function.Surjective,not_forall,not_exists] at hSurj
      obtain ⟨j,hMissing⟩ := hSurj
      choose pred hPred using fun i => Fin.exists_succAbove_eq (hMissing i)
      let e₀ : Fin r ↪ Fin s := ⟨pred,fun i i' hh => e.injective
        ((hPred i).symm.trans ((congrArg j.succAbove hh).trans (hPred i')))⟩
      have hMono₀ : StrictMono e₀ := by
        intro i i' hi
        apply (Fin.strictMono_succAbove j).lt_iff_lt.mp
        change j.succAbove (pred i) < j.succAbove (pred i')
        rw [hPred i,hPred i']
        exact hMono hi
      obtain ⟨p⟩ := ih hMono₀
      have he : e = e₀.trans j.succAboveEmb :=
        Function.Embedding.ext fun i => (hPred i).symm
      rw [he]
      exact ⟨.insert p j⟩

/-- Keep the old mask if it selects only original slots. -/
def project : ∀ {s : ℕ} {e : Fin r ↪ Fin s}, OldRowInsertion r s e →
    Finset (Fin s) → Option (Finset (Fin r))
  | _,_,.refl,Q => some Q
  | _,_,.insert p j,Q => (eraseAbsentMask j Q).bind (project p)

theorem map_of_project_eq_some (p : OldRowInsertion r s e) :
    ∀ {Q : Finset (Fin s)} {P : Finset (Fin r)}, p.project Q = some P → P.map e = Q := by
  induction p with
  | refl =>
    intro Q P h
    have hEq : Q = P := Option.some.inj h
    simp [hEq]
  | insert p j ih =>
    intro Q P h
    cases ha : eraseAbsentMask j Q with
    | none =>
      simp [project,ha] at h
    | some R =>
      have hR : p.project R = some P := by simpa [project,ha] using h
      rw [←Finset.map_map,ih hR]
      exact map_of_eraseAbsentMask_eq_some ha

/-- A discarded mask selects at least one slot outside the chronological
embedding of the old list. -/
theorem exists_unmatched_of_project_eq_none (p : OldRowInsertion r s e) :
    ∀ {Q : Finset (Fin s)}, p.project Q = none →
      ∃ j ∈ Q,∀ i, e i ≠ j := by
  induction p with
  | refl =>
    intro Q h
    simp [project] at h
  | insert p j ih =>
    intro Q h
    cases ha : eraseAbsentMask j Q with
    | none =>
      exact ⟨j,(eraseAbsentMask_eq_none_iff j Q).mp ha,fun i => j.succAbove_ne _⟩
    | some R =>
      have hR : p.project R = none := by simpa [project,ha] using h
      obtain ⟨k,hk,hMissing⟩ := ih hR
      refine ⟨j.succAbove k,?_,?_⟩
      · rw [←map_of_eraseAbsentMask_eq_some ha]
        exact Finset.mem_map.mpr ⟨k,hk,rfl⟩
      · intro i hi
        exact hMissing i (j.succAboveEmb.injective hi)

/-- The whole descending incidence schedule projects exactly through any
finite sequence of inserted absent old slots. -/
theorem descendingMaskLabels_project (p : OldRowInsertion r s e) (q : ℕ) :
    (descendingMaskLabels (orderedMaskLevel s) q).filterMap p.project =
      descendingMaskLabels (orderedMaskLevel r) q := by
  induction p with
  | refl => simp [project]
  | insert p j ih =>
    change (descendingMaskLabels (orderedMaskLevel _) q).filterMap
      (fun Q => (eraseAbsentMask j Q).bind p.project) = _
    rw [←List.filterMap_filterMap,descendingMaskLabels_eraseAbsentMask,ih]

theorem length_le (p : OldRowInsertion r s e) : r ≤ s := by
  induction p with
  | refl => rfl
  | insert _ _ ih => omega

/-- The two original row lengths may each supply their own cap. -/
theorem descendingMaskLabels_project_of_caps (p : OldRowInsertion r s e)
    {q q' : ℕ} (hQ : r ≤ q) (hQ' : s ≤ q') :
    (descendingMaskLabels (orderedMaskLevel s) q').filterMap p.project =
      descendingMaskLabels (orderedMaskLevel r) q := by
  rw [p.descendingMaskLabels_project q',
    descendingMaskLabels_eq_at_length (p.length_le.trans hQ'),
    descendingMaskLabels_eq_at_length hQ]

end OldRowInsertion
end
end Hironaka.HironakaG4MaskScheduleEmptyRows
