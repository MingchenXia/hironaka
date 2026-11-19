import Hironaka.Resolution.HironakaActualIndexedBoundaryContinuation
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3IndexedBoundaryFiniteWindow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation

/-- Every point of an indexed locally finite SNC boundary has an open window
on which a finite injective list contains every boundary member that meets
that window; the list is itself SNC. -/
theorem exists_finite_boundary_window {n : ℕ} {X : CMfd.{u} n} {ι : Type v}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) (x : X) :
    ∃ (U : Opens X) (k : ℕ) (e : Fin k ↪ ι), x ∈ U ∧
      IsSNCDivisor n (finiteBoundary D e) ∧
      (∀ i, (D i ∩ (U : Set X)).Nonempty → ∃ j, e j = i) ∧
      (∀ y ∈ U, (∃ i, y ∈ D i) ↔ ∃ j, y ∈ D (e j)) := by
  classical
  obtain ⟨T,hT,hfin⟩ := hD.1 x
  obtain ⟨O,hOT,hOo,hxO⟩ := mem_nhds_iff.mp hT
  let U : Opens X := ⟨O,hOo⟩
  let S : Set ι := {i | (D i ∩ O).Nonempty}
  have hS : S.Finite := hfin.subset (fun i hi => hi.mono (inter_subset_inter_right _ hOT))
  let : Fintype S := hS.fintype
  let e : Fin (Fintype.card S) ↪ ι :=
    ⟨fun j => ((Fintype.equivFin S).symm j).val,
      fun i j hij => (Fintype.equivFin S).symm.injective (Subtype.ext hij)⟩
  have hhit : ∀ i, (D i ∩ (U : Set X)).Nonempty → ∃ j, e j = i := by
    intro i hi
    refine ⟨(Fintype.equivFin S) ⟨i,hi⟩,?_⟩
    change ((Fintype.equivFin S).symm ((Fintype.equivFin S) ⟨i,hi⟩)).val = i
    rw [Equiv.symm_apply_apply]
  refine ⟨U,Fintype.card S,e,hxO,isSNCDivisor_finiteBoundary D hD e,hhit,?_⟩
  intro y hy
  constructor
  · rintro ⟨i,hyi⟩
    obtain ⟨j,rfl⟩ := hhit i ⟨y,hyi,hy⟩
    exact ⟨j,hyi⟩
  · rintro ⟨j,hj⟩
    exact ⟨e j,hj⟩
end
end Hironaka.HironakaG3IndexedBoundaryFiniteWindow
