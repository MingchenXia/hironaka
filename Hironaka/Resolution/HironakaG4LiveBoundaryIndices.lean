import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Basic

/-! Literal position correspondence for an ordered boundary after empty slots are removed. -/

set_option autoImplicit false

namespace Hironaka.HironakaG4LiveBoundaryIndices

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Every retained position in the nonempty boundary corresponds to its
original position in order. Precisely the empty slots are skipped. -/
theorem exists_live_boundary_embedding {X : Type*} (E : List (Set X)) :
    let L := E.filter fun H => decide H.Nonempty
    ∃ e : Fin L.length ↪ Fin E.length, StrictMono e ∧
      (∀ i, E.get (e i) = L.get i) ∧
      ∀ j, (∀ i, e i ≠ j) → E.get j = ∅ := by
  let L := E.filter fun H => decide H.Nonempty
  let I := (List.finRange E.length).filter fun j => decide (E.get j).Nonempty
  have hMap : I.map E.get = L := by
    calc
      I.map E.get = ((List.finRange E.length).map E.get).filter (fun H => decide H.Nonempty) :=
        (List.filter_map (f := E.get) (p := fun H => decide H.Nonempty)
          (l := List.finRange E.length)).symm
      _ = L := congrArg (List.filter fun H => decide H.Nonempty) (List.map_get_finRange E)
  have hLen : L.length = I.length := by rw [← hMap, List.length_map]
  have hSorted : I.SortedLT :=
    List.sortedLT_iff_pairwise.mpr ((List.sortedLT_finRange E.length).pairwise.sublist List.filter_sublist)
  let c := finCongr hLen
  have hMono : StrictMono (fun i => I.get (c i)) := fun _ _ hij => hSorted.strictMono_get hij
  let e : Fin L.length ↪ Fin E.length := ⟨fun i => I.get (c i), hMono.injective⟩
  refine ⟨e, hMono, ?_, ?_⟩
  · intro i
    have hi : i.val < (I.map E.get).length := hMap.symm ▸ i.isLt
    simpa only [e, c, Function.Embedding.coeFn_mk, List.get_eq_getElem, List.getElem_map,
      finCongr_apply_coe] using List.get_of_eq hMap ⟨i.val, hi⟩
  · intro j hSkip
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hj
    have hMem : j ∈ I := List.mem_filter.mpr ⟨List.mem_finRange j, decide_eq_true hj⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hMem
    apply hSkip (c.symm i)
    simpa only [e, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] using hi

end
end Hironaka.HironakaG4LiveBoundaryIndices
