import Hironaka.Resolution.HironakaG8ClassStepPerm

/-!
# Local equivalence after moving one boundary slot to the front

The same indexed slot is moved in both records. The remaining ordered list
retains every other slot, including repeated empty members.
-/
set_option autoImplicit false

universe u

namespace Hironaka.HironakaG8CaseTLocalReorder

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal HironakaG8LocalHistory HironakaG8ClassStepPerm

noncomputable section

/-- Moving an indexed slot to the front preserves all the other slots. -/
theorem get_cons_eraseIdx_perm {α : Type*} (E : List α) (i : Fin E.length) :
    (E.get i :: E.eraseIdx i.val).Perm E := by
  simpa only [List.get_eq_getElem] using (List.getElem_cons_eraseIdx_perm i.isLt)

/-- Simultaneously moving the same indexed boundary member to the front
preserves the full local equivalence, including projection tests. -/
theorem locWPEquiv_get_cons_eraseIdx
    {n : ℕ} {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (h : LocWPEquiv A B) (i : Fin A.E.length) :
    LocWPEquiv { A with E := A.E.get i :: A.E.eraseIdx i.val }
      { B with E := A.E.get i :: A.E.eraseIdx i.val } := by
  exact locEquiv_perm rfl h (get_cons_eraseIdx_perm A.E i)

end
end Hironaka.HironakaG8CaseTLocalReorder
