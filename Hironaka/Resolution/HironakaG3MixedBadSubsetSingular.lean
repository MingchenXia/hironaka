import Hironaka.Resolution.HironakaG3RegularUnionUniqueComponent
import Hironaka.Resolution.HironakaG3IndexedMixedBad
import Hironaka.Resolution.HironakaG34LocalIdentityCover
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.AnalyticIrreducibleComponents
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedBadSubsetSingular
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3IndexedMixedBad
  HironakaActualLocallyFiniteBoundary HironakaG34LocalIdentityCover ClosureDifferenceAnalytic
  HironakaG3RegularUnionUniqueComponent


theorem indexed_mixed_bad_subset_singular {n d : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier))
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (W : Set X) (hW : W = ⋃ i, (V i).carrier) :
    indexedMixedBad V ⊆ W \ regularLocus (n := n) W d := by
  intro x hx
  have hxW : x ∈ W := by
    rw [hW]
    rcases hx with hx | hx
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i,hi.1⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hi
      obtain ⟨hij,hxij⟩ := mem_iUnion.mp hj
      exact mem_iUnion.mpr ⟨i,hxij.1⟩
  refine ⟨hxW,?_⟩
  intro hxReg
  obtain ⟨i,hxi,hReg,hUnique⟩ := regular_union_unique_component V hLF hDistinct W hW hxReg
  rcases hx with hx | hx
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have hji : j = i := hUnique j hj.1
    subst j
    exact hj.2 hReg
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hj
    obtain ⟨hjk,hxjk⟩ := mem_iUnion.mp hk
    exact hjk ((hUnique j hxjk.1).trans (hUnique k hxjk.2).symm)
end
end Hironaka.HironakaG3MixedBadSubsetSingular
