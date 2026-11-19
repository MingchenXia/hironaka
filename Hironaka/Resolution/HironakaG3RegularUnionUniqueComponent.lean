import Hironaka.Blowup.BlowupTowers
import Hironaka.Blowup.BlowupSequences
import Hironaka.Resolution.HironakaG34LocalIdentityCover
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.AnalyticIrreducibleComponents
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3RegularUnionUniqueComponent
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG34LocalIdentityCover ClosureDifferenceAnalytic

theorem regular_union_unique_component {n d : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier))
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (W : Set X) (hW : W = ⋃ i, (V i).carrier) {x : X}
    (hx : RegularAtDim (n := n) W x d) :
    ∃ i, x ∈ (V i).carrier ∧ RegularAtDim (n := n) (V i).carrier x (V i).dim ∧
      ∀ j, x ∈ (V j).carrier → j = i := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
  let s := (hLF.finite_nonempty_inter_compact hK).toFinset
  have hCov : ∀ᶠ y in 𝓝 x, y ∈ W → ∃ i : {i // i ∈ s}, y ∈ (V i.val).carrier := by
    filter_upwards [hxK] with y hy hyW
    rw [hW] at hyW
    obtain ⟨i,hyi⟩ := mem_iUnion.mp hyW
    have hi : i ∈ s := (hLF.finite_nonempty_inter_compact hK).mem_toFinset.mpr ⟨y,hyi,hy⟩
    exact ⟨⟨i,hi⟩,hyi⟩
  obtain ⟨i,hi⟩ := exists_eventually_subset_of_cover hx (fun i : {i // i ∈ s} => (V i.val).carrier)
    (fun i => (V i.val).irreducible_carrier.analytic) hCov
  obtain ⟨O,hOsub,hOopen,hxO⟩ := mem_nhds_iff.mp hi
  have hLoc : W ∩ O = (V i.val).carrier ∩ O := by
    ext y
    constructor
    · rintro ⟨hyW,hyO⟩
      exact ⟨hOsub hyO hyW,hyO⟩
    · rintro ⟨hyV,hyO⟩
      refine ⟨?_,hyO⟩
      rw [hW]
      exact mem_iUnion.mpr ⟨i.val,hyV⟩
  have hxVi : x ∈ (V i.val).carrier := hOsub hxO hx.2.1
  have hxReg : RegularAtDim (n := n) (V i.val).carrier x d :=
    RegularPointDimension.regularAtDim_of_inter_eq hOopen hxO hLoc hx
  have hd : d = (V i.val).dim := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim (V i.val) hxReg
  refine ⟨i.val,hxVi,?_,?_⟩
  · rw [← hd]
    exact hxReg
  · intro j hxVj
    by_contra hji
    have hInt := eq_of_subset_of_inter_open_subset
      ((V j).irreducible_carrier.analytic.inter (V i.val).irreducible_carrier.analytic)
      (V j).irreducible_carrier inter_subset_left hOopen ⟨x,hxVj,hxO⟩ (by
        rintro y ⟨hyV,hyO⟩
        refine ⟨hyV,hOsub hyO ?_⟩
        rw [hW]
        exact mem_iUnion.mpr ⟨j,hyV⟩)
    apply hDistinct j i.val hji
    intro y hy
    rw [← hInt] at hy
    exact hy.2

end
end Hironaka.HironakaG3RegularUnionUniqueComponent
