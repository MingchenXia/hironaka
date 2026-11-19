import Hironaka.Resolution.HironakaActualSelectedOldBoundaryCleanup
import Hironaka.Invariant.MemberInterLocusAlong

/-! Fixed ORIGINAL old positions for finite geometric cleanup. These raw
incidences are not the original distinct proper ideal-germ defect count. -/
set_option autoImplicit false
open Set Classical
universe u
namespace Hironaka.HironakaActualOldIndexCleanupTransport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong
variable {n : ℕ} {X Y Z : CMfd.{u} n}

def incidentIndices {k : ℕ} (H : Fin k → Set X) (x : X) : Finset (Fin k):=
  Finset.univ.filter fun j=>x∈H j

def selectedIntersection {k : ℕ} (N : Set X) (H : Fin k → Set X) (s : Finset (Fin k)) : Set X:=
  {x | x∈N ∧ ∀j∈s,x∈H j}

def selectedStrictIntersection (N : Set X) (O : List (Set X)) (T : BlowupTower X Y)
    (s : Finset (Fin O.length)) : Set Y:=
  selectedIntersection (strictAlong T N) (fun j=>strictAlong T (O.get j)) s

def maximalSelections (k m : ℕ) : List (Finset (Fin k)):=
  ((Finset.univ : Finset (Fin k)).powerset.filter fun s=>s.card=m).toList

theorem mem_maximalSelections_iff {k m : ℕ} {s : Finset (Fin k)} :
    s∈maximalSelections k m ↔ s.card=m := by
  simp [maximalSelections]

theorem selectedStrictIntersection_subset_preimage {N : Set X} {O : List (Set X)}
    (hN : IsClosed N) (hO : ∀H∈O,IsClosed H) (T : BlowupTower X Y)
    (s : Finset (Fin O.length)) :
    selectedStrictIntersection N O T s⊆T.proj ⁻¹' selectedIntersection N O.get s := by
  rintro y ⟨hyN,hyO⟩
  exact ⟨strictAlong_subset_preimage T hN hyN,
    fun j hj=>strictAlong_subset_preimage T (hO _ (List.get_mem O j)) (hyO j hj)⟩

theorem selectedStrictIntersection_append_subset {N : Set X} {O : List (Set X)}
    (hN : IsClosed N) (hO : ∀H∈O,IsClosed H) (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (s : Finset (Fin O.length)) :
    selectedStrictIntersection N O (T.append S) s⊆S.proj ⁻¹' selectedStrictIntersection N O T s := by
  rintro z ⟨hzN,hzO⟩
  rw [strictAlong_append] at hzN
  refine ⟨strictAlong_subset_preimage S (isClosed_strictAlong T hN) hzN,fun j hj=>?_⟩
  have hjz:=hzO j hj
  change z∈strictAlong (T.append S) (O.get j) at hjz
  rw [strictAlong_append] at hjz
  exact strictAlong_subset_preimage S (isClosed_strictAlong T (hO _ (List.get_mem O j))) hjz

theorem selectedStrictIntersection_empty_append {N : Set X} {O : List (Set X)}
    (hN : IsClosed N) (hO : ∀H∈O,IsClosed H) (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (s : Finset (Fin O.length)) (hEmpty : selectedStrictIntersection N O T s=∅) :
    selectedStrictIntersection N O (T.append S) s=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h:=selectedStrictIntersection_append_subset hN hO T S s hz
  rw [hEmpty] at h
  exact h

theorem incident_card_le_initial {O : List (Set X)}
    (hO : ∀H∈O,IsClosed H) (T : BlowupTower X Y) (y : Y) :
    (incidentIndices (fun j=>strictAlong T (O.get j)) y).card≤
      (incidentIndices O.get (T.proj y)).card := by
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,strictAlong_subset_preimage T (hO _ (List.get_mem O j))
    (Finset.mem_filter.mp hj).2⟩

/-- The index equivalence is the identity on the SAME original position. -/
def strictIndex (O : List (Set X)) (T : BlowupTower X Y) :
    Fin O.length ≃ Fin (O.map (strictAlong T)).length where
  toFun j:=⟨j.val,by rw [List.length_map];exact j.isLt⟩
  invFun j:=⟨j.val,by simpa only [List.length_map] using j.isLt⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem get_strictIndex (O : List (Set X)) (T : BlowupTower X Y) (j : Fin O.length) :
    (O.map (strictAlong T)).get (strictIndex O T j)=strictAlong T (O.get j) := by
  simp [strictIndex]

theorem selectedIntersection_current_eq (N : Set X) (O : List (Set X)) (T : BlowupTower X Y)
    (s : Finset (Fin O.length)) :
    selectedIntersection (strictAlong T N) (O.map (strictAlong T)).get
      (s.map (strictIndex O T).toEmbedding)=selectedStrictIntersection N O T s := by
  ext y
  constructor
  · rintro ⟨hyN,hy⟩
    refine ⟨hyN,fun j hj=>?_⟩
    have h:=hy (strictIndex O T j) (Finset.mem_map.mpr ⟨j,hj,rfl⟩)
    change y∈(O.map (strictAlong T)).get (strictIndex O T j) at h
    rw [get_strictIndex] at h
    exact h
  · rintro ⟨hyN,hy⟩
    refine ⟨hyN,fun j hj=>?_⟩
    obtain ⟨j₀,hj₀,rfl⟩:=Finset.mem_map.mp hj
    change y∈(O.map (strictAlong T)).get (strictIndex O T j₀)
    rw [get_strictIndex]
    exact hy j₀ hj₀

theorem incident_card_current_eq (O : List (Set X)) (T : BlowupTower X Y) (y : Y) :
    (incidentIndices (O.map (strictAlong T)).get y).card=
      (incidentIndices (fun j=>strictAlong T (O.get j)) y).card := by
  have hEq : incidentIndices (O.map (strictAlong T)).get y=
      (incidentIndices (fun j=>strictAlong T (O.get j)) y).map (strictIndex O T).toEmbedding := by
    ext j
    constructor
    · intro hj
      refine Finset.mem_map.mpr ⟨(strictIndex O T).symm j,?_,by simp⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hGet:=get_strictIndex O T ((strictIndex O T).symm j)
      rw [Equiv.apply_symm_apply] at hGet
      change y∈strictAlong T (O.get ((strictIndex O T).symm j))
      rw [←hGet]
      exact (Finset.mem_filter.mp hj).2
    · intro hj
      obtain ⟨j₀,hj₀,rfl⟩:=Finset.mem_map.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change y∈(O.map (strictAlong T)).get (strictIndex O T j₀)
      rw [get_strictIndex]
      exact (Finset.mem_filter.mp hj₀).2
  rw [hEq,Finset.card_map]

theorem incident_bound_drop_of_selected_empty {k m : ℕ} {N : Set X} {H : Fin k → Set X}
    (hBound : ∀x∈N,(incidentIndices H x).card≤m+1)
    (hEmpty : ∀s∈maximalSelections k (m+1),selectedIntersection N H s=∅) :
    ∀x∈N,(incidentIndices H x).card≤m := by
  intro x hx
  by_contra hNot
  have hCard : (incidentIndices H x).card=m+1:=by have h:=hBound x hx;omega
  have hErased:=hEmpty (incidentIndices H x) (mem_maximalSelections_iff.mpr hCard)
  have hMem : x∈selectedIntersection N H (incidentIndices H x):=
    ⟨hx,fun _ hj=>(Finset.mem_filter.mp hj).2⟩
  rw [hErased] at hMem
  exact hMem

end
end Hironaka.HironakaActualOldIndexCleanupTransport
