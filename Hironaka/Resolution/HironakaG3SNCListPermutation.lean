import Hironaka.Resolution.HironakaActualBoundarySlotReindex
import Mathlib.Data.List.Perm.Basic
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SNCListPermutation
universe u
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaActualBoundarySlotReindex

/-- A positional permutation of a list preserves SNC, including repeated
empty entries: no value-level injectivity is assumed. -/
theorem snc_map_perm_finRange {n : ℕ} {X : CMfd.{u} n} (E : List (Set X))
    (L : List (Fin E.length)) (hL : L.Perm (List.finRange E.length)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor n (L.map E.get) := by
  have hn : L.Nodup := hL.nodup_iff.mpr (List.nodup_finRange _)
  let he : Fin L.length ≃ Fin E.length := Equiv.ofBijective L.get
    ⟨List.nodup_iff_injective_get.mp hn, fun i => by
      have hi : i ∈ L := hL.symm.subset (List.mem_finRange i)
      exact List.mem_iff_get.mp hi⟩
  let J := L.map E.get
  have hlen : J.length = L.length := by simp [J]
  let e : Fin J.length ≃ Fin E.length := (finCongr hlen).trans he
  have hget : ∀ i : Fin J.length, J.get i = E.get (e i) := by
    intro i
    simp only [J, List.get_eq_getElem, List.getElem_map]
    change E.get (L.get ⟨i.val, by simpa [J] using i.isLt⟩) = E.get (he (Fin.cast hlen i))
    rfl
  exact (snc_reindex_iff e hget).mpr hE

/-- Every permutation of an SNC divisor is SNC, preserving multiplicities. -/
theorem isSNCDivisor_of_perm {n : ℕ} {X : CMfd.{u} n} {E F : List (Set X)}
    (hE : IsSNCDivisor n E) (hPerm : F.Perm E) : IsSNCDivisor n F := by
  have hMap : F.Perm ((List.finRange E.length).map E.get) := by
    simpa only [List.map_get_finRange] using hPerm
  have hLift : Relation.Comp (fun a b => a = List.map E.get b) List.Perm F (List.finRange E.length) := by
    rw [List.eq_map_comp_perm]
    exact hMap
  obtain ⟨L,hEq,hL⟩ := hLift
  rw [hEq]
  exact snc_map_perm_finRange E L hL hE
end
end Hironaka.HironakaG3SNCListPermutation
