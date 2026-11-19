import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.Blowup.NormalCrossingsInvariance

/-! Explicit finite old/born/horizontal slot transport and native ordinary
tests. Weak equivalence is transported only by replacing BOTH boundaries
with the same literal list. No canonical invariant/history-value assertion.
Blueprint FIRST: `hironaka-actual-boundary-slot-reindex.tex`. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualBoundarySlotReindex
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance MarkedIdealEquivalence.MarkedIdeal

/-- The explicit standard-to-chronological slot bijection, retaining duplicates. -/
def boundarySlotEquiv {α : Type v} (old born : List α) (H : α) :
    Fin ((old ++ born ++ [H]).length) ≃ Fin ((old ++ [H] ++ born).length) where
  toFun i := ⟨if i.val < old.length then i.val
      else if i.val < old.length + born.length then i.val + 1 else old.length, by
    have hi := i.isLt
    simp only [List.length_append, List.length_singleton] at hi ⊢
    split_ifs <;> omega⟩
  invFun i := ⟨if i.val < old.length then i.val
      else if i.val = old.length then old.length + born.length else i.val - 1, by
    have hi := i.isLt
    simp only [List.length_append, List.length_singleton] at hi ⊢
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt
    simp only [List.length_append, List.length_singleton] at hi
    dsimp
    split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    have hi := i.isLt
    simp only [List.length_append, List.length_singleton] at hi
    dsimp
    split_ifs <;> omega

theorem boundarySlotEquiv_value {α : Type v} (old born : List α) (H : α)
    (i : Fin ((old ++ born ++ [H]).length)) :
    (boundarySlotEquiv old born H i).val =
      if i.val < old.length then i.val
      else if i.val < old.length + born.length then i.val + 1 else old.length := rfl

theorem boundarySlotEquiv_symm_value {α : Type v} (old born : List α) (H : α)
    (i : Fin ((old ++ [H] ++ born).length)) :
    ((boundarySlotEquiv old born H).symm i).val =
      if i.val < old.length then i.val
      else if i.val = old.length then old.length + born.length else i.val - 1 := rfl

theorem boundarySlotEquiv_get {α : Type v} (old born : List α) (H : α)
    (i : Fin ((old ++ born ++ [H]).length)) :
    (old ++ born ++ [H]).get i = (old ++ [H] ++ born).get (boundarySlotEquiv old born H i) := by
  simp only [List.get_eq_getElem, boundarySlotEquiv_value]
  by_cases ho : i.val < old.length
  · simp [ho]
  · by_cases hb : i.val < old.length + born.length
    · simp only [if_neg ho,if_pos hb]
      rw [List.getElem_append_left (by simpa only [List.length_append] using hb)]
      rw [List.getElem_append_right (show old.length ≤ i.val by omega)]
      rw [List.getElem_append_right (show (old ++ [H]).length ≤ i.val+1 by
        simp only [List.length_append,List.length_singleton]
        omega)]
      congr 1
      simp only [List.length_append,List.length_singleton]
      omega
    · have hi := i.isLt
      simp only [List.length_append, List.length_singleton] at hi
      have he : i.val = old.length + born.length := by omega
      simp [he]

variable {n : ℕ} {X : CMfd.{u} n} {E F : List (Set X)}

private theorem snc_reindex (e : Fin E.length ≃ Fin F.length)
    (he : ∀ i, E.get i = F.get (e i)) (h : IsSNCDivisor n E) : IsSNCDivisor n F := by
  have hget (j : Fin F.length) : F.get j = E.get (e.symm j) := by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm
  refine ⟨?_,?_⟩
  · intro H hH
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hH
    rw [hget]
    exact h.1 _ (List.get_mem _ _)
  · intro x
    obtain ⟨S,hcoord,hcard,hinj⟩ := h.2 x
    refine ⟨S ∘ e.symm, IsCoordinateFamilyAt.reindex hcoord e.symm hget (fun _ => rfl),?_,?_⟩
    · intro j hj
      exact hcard (e.symm j) (hget j ▸ hj)
    · intro i hi j hj hij
      apply e.symm.injective
      have hiE : x ∈ E.get (e.symm i) := by rw [←hget i]; exact hi
      have hjE : x ∈ E.get (e.symm j) := by rw [←hget j]; exact hj
      exact hinj hiE hjE hij

theorem snc_reindex_iff (e : Fin E.length ≃ Fin F.length)
    (he : ∀ i, E.get i = F.get (e i)) : IsSNCDivisor n E ↔ IsSNCDivisor n F :=
  ⟨snc_reindex e he, snc_reindex e.symm (fun j => by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm)⟩

private theorem centre_nc_reindex (e : Fin E.length ≃ Fin F.length)
    (he : ∀ i, E.get i = F.get (e i)) (C : Set X)
    (h : HasNormalCrossings n C E) : HasNormalCrossings n C F := by
  have hget (j : Fin F.length) : F.get j = E.get (e.symm j) := by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm
  intro x hx
  obtain ⟨S₀,S,hcoord,hcard⟩ := h x hx
  refine ⟨S₀,S ∘ e.symm,?_,?_⟩
  · apply IsCoordinateFamilyAt.reindex hcoord (Option.map e.symm)
    · intro o
      cases o with
      | none => rfl
      | some j => exact hget j
    · intro o
      cases o <;> rfl
  · intro j hj
    exact hcard (e.symm j) (hget j ▸ hj)

theorem centre_nc_reindex_iff (e : Fin E.length ≃ Fin F.length)
    (he : ∀ i, E.get i = F.get (e i)) (C : Set X) :
    HasNormalCrossings n C E ↔ HasNormalCrossings n C F :=
  ⟨centre_nc_reindex e he C, centre_nc_reindex e.symm (fun j => by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm) C⟩

private theorem transverse_reindex (e : Fin E.length ≃ Fin F.length)
    (he : ∀ i, E.get i = F.get (e i)) (N : Set X)
    (h : IsTransverse n N E) : IsTransverse n N F := by
  have hget (j : Fin F.length) : F.get j = E.get (e.symm j) := by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm
  intro x hx
  obtain ⟨S₀,S,hcoord,hcard⟩ := h x hx
  refine ⟨S₀,S ∘ e.symm,?_,?_⟩
  · apply IsCoordinateFamilyAt.reindex hcoord (Option.map e.symm)
    · intro o
      cases o with
      | none => rfl
      | some j => exact hget j
    · intro o
      cases o <;> rfl
  · intro j hj
    exact hcard (e.symm j) (hget j ▸ hj)

theorem transverse_reindex_iff (e : Fin E.length ≃ Fin F.length)
    (he : ∀ i, E.get i = F.get (e i)) (N : Set X) :
    IsTransverse n N E ↔ IsTransverse n N F :=
  ⟨transverse_reindex e he N, transverse_reindex e.symm (fun j => by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm) N⟩

private def growSlots {p q : ℕ} (e : Fin p ≃ Fin q) : Fin (p+1) ≃ Fin (q+1) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)

private theorem growSlots_old {p q : ℕ} (e : Fin p ≃ Fin q) (i : Fin p) :
    growSlots e i.castSucc = (e i).castSucc := by
  simp [growSlots]
  rfl

private theorem growSlots_last {p q : ℕ} (e : Fin p ≃ Fin q) :
    growSlots e (Fin.last p) = Fin.last q := by
  simp [growSlots]
  rfl

private theorem map_append_slots {α β : Type*} (A B : List α)
    (e : Fin A.length ≃ Fin B.length) (he : ∀ i, A.get i = B.get (e i))
    (f : α → β) (H : β) :
    ∃ e' : Fin (A.map f ++ [H]).length ≃ Fin (B.map f ++ [H]).length,
      ∀ i, (A.map f ++ [H]).get i = (B.map f ++ [H]).get (e' i) := by
  have hA : (A.map f ++ [H]).length = A.length+1 := by simp
  have hB : (B.map f ++ [H]).length = B.length+1 := by simp
  let e' := (finCongr hA).trans ((growSlots e).trans (finCongr hB).symm)
  have haux (j : Fin (A.length+1)) :
      (A.map f ++ [H]).get (Fin.cast hA.symm j) =
        (B.map f ++ [H]).get (Fin.cast hB.symm (growSlots e j)) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [growSlots_last, List.get_eq_getElem]
    · rw [growSlots_old]
      simpa [List.get_eq_getElem, List.getElem_append, i.isLt, (e i).isLt]
        using congrArg f (he i)
  refine ⟨e',fun i => ?_⟩
  simpa [e'] using haux (Fin.cast hA i)

private def Related (M N : MarkedIdeal n X) : Prop :=
  M.N = N.N ∧ M.ideal = N.ideal ∧ M.d = N.d ∧
    ∃ e : Fin M.E.length ≃ Fin N.E.length, ∀ i, M.E.get i = N.E.get (e i)

private theorem related_cosupp {M N : MarkedIdeal n X} (h : Related M N) :
    M.cosupp = N.cosupp := by
  rcases h with ⟨hN,hI,hd,_⟩
  simp only [cosupp,hN,hI,hd]

private theorem related_admissible {M N : MarkedIdeal n X} (h : Related M N) (C : Set X) :
    M.IsAdmissibleCentre C ↔ N.IsAdmissibleCentre C := by
  have hcosupp := related_cosupp h
  obtain ⟨_,_,_,e,he⟩ := h
  simp only [IsAdmissibleCentre, hcosupp, centre_nc_reindex_iff e he C]

private theorem related_transform {M N : MarkedIdeal n X} (h : Related M N)
    {Y : CMfd.{u} n} (C : Set X) (π : Y → X) :
    Related (M.geoTransform C π) (N.geoTransform C π) := by
  rcases h with ⟨hN,hI,hd,e,he⟩
  refine ⟨?_,?_,hd,?_⟩
  · simp only [geoTransform_N,hN]
  · simp only [geoTransform_ideal,hN,hI,hd]
  · exact map_append_slots M.E N.E e he (BlowupStrictSubmanifold.geoStrictTransform π C) (π ⁻¹' C)

/-- Exact carrier/whole ideal/mark and finite-slot transport give the SAME
native tests and unconditional terminal cosupport equality on every tower. -/
theorem native_tests_and_cosupp_reindex
    {M N : MarkedIdeal n X} (hN : M.N = N.N) (hI : M.ideal = N.ideal) (hd : M.d = N.d)
    (e : Fin M.E.length ≃ Fin N.E.length) (he : ∀ i, M.E.get i = N.E.get (e i))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (IsGeoTestTower M T ↔ IsGeoTestTower N T) ∧
      (geoTransformAlong M T).cosupp = (geoTransformAlong N T).cosupp := by
  have hbase : Related M N := ⟨hN,hI,hd,e,he⟩
  have hstage : Related (geoTransformAlong M T) (geoTransformAlong N T) ∧
      (IsGeoTestTower M T ↔ IsGeoTestTower N T) := by
    induction T with
    | refl => exact ⟨hbase,Iff.rfl⟩
    | step T C π hπ ih =>
      exact ⟨related_transform ih.1 C π, and_congr ih.2 (related_admissible ih.1 C)⟩
  exact ⟨hstage.2,related_cosupp hstage.1⟩

/-- BOTH boundaries become the same literal F; no weak equivalence is
formed between a record and a copy with an unequal ordered boundary. -/
theorem simultaneous_boundary_wEquiv {M N : MarkedIdeal n X}
    (h : WEquiv M N) (F : List (Set X)) (e : Fin M.E.length ≃ Fin F.length)
    (he : ∀ i, M.E.get i = F.get (e i)) :
    WEquiv {M with E := F} {N with E := F} := by
  have hslotsN : ∃ eN : Fin N.E.length ≃ Fin F.length,
      ∀ i, N.E.get i = F.get (eN i) := by
    rw [←h.1]
    exact ⟨e,he⟩
  obtain ⟨eN,heN⟩ := hslotsN
  refine ⟨rfl,fun T => ?_⟩
  have hM := native_tests_and_cosupp_reindex (M := M) (N := {M with E := F})
    rfl rfl rfl e he T
  have hN := native_tests_and_cosupp_reindex (M := N) (N := {N with E := F})
    rfl rfl rfl eN heN T
  refine ⟨hM.1.symm.trans ((h.2 T).1.trans hN.1),fun ht => ?_⟩
  exact hM.2.symm.trans (((h.2 T).2 (hM.1.mpr ht)).trans hN.2)

end
end Hironaka.HironakaActualBoundarySlotReindex
