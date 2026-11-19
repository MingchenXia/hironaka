import Hironaka.Resolution.HironakaDimensionGlobalComponents
import Hironaka.Blowup.BlowupTowers
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3PureGlobalComponents
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers GlobalComponents RegularLocusComponent
  HironakaDimensionGlobalComponents

/-- A dense pure regular locus determines the dimension of every regular point. -/
theorem regular_dimension_of_dense_pure {n d : ℕ} {X : CMfd.{0} n} (W : Set X)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    {x : X} {k : ℕ} (hx : RegularAtDim (n := n) W x k) : k = d := by
  obtain ⟨y,hy,hD⟩ := mem_closure_iff_nhds.mp (hPure hx.2.1) _
    (RegularPatchNeighborhood.eventually_regularAtDim hx)
  exact RegularPointDimension.eq_of_regularAtDim (hy hD.2.1) hD

/-- Two distinct genuine global analytic components are incomparable. -/
theorem global_components_incomparable {n : ℕ} {X : CMfd.{0} n} (W : Set X)
    (B C : globalComponents (n := n) W) (hBC : (B : Set X) ⊆ C) : B = C := by
  obtain ⟨b,⟨kb,hb⟩,hB⟩ := B.property
  obtain ⟨c,⟨kc,hc⟩,hC⟩ := C.property
  have hbC : b ∈ closure (component (n := n) W c) := by
    apply hC ▸ hBC
    rw [hB]
    exact subset_closure (mem_component_self hb)
  obtain ⟨O,hO,hbO,hOsub⟩ := exists_open_inter_subset_component hb (mem_component_self hb)
  obtain ⟨z,hzO,hzC⟩ := mem_closure_iff.mp hbC O hO hbO
  have hzB : z ∈ component (n := n) W b :=
    hOsub ⟨component_subset W c hzC,hzO⟩
  have he : component (n := n) W b = component (n := n) W c := by
    exact (connectedComponentIn_eq hzB).trans (connectedComponentIn_eq hzC).symm
  apply Subtype.ext
  rw [hB,hC,he]

/-- Actual global irreducible components provide the finite-local indexed
family of the original pure analytic target, with no boundary avoidance. -/
theorem exists_pure_global_component_family {n d : ℕ} {X : CMfd.{0} n} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) (hd : d < n)
    (hPure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (V : globalComponents (n := n) W → ClosedIrreducibleAnalyticSubvariety n X),
      (∀ i, (V i).carrier = (i : Set X)) ∧
      (∀ i, (V i).dim = d) ∧
      LocallyFinite (fun i => (V i).carrier) ∧
      (∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier) ∧
      (⋃ i, (V i).carrier) = W := by
  have hEach : ∀ B : globalComponents (n := n) W,
      ∃ V : ClosedIrreducibleAnalyticSubvariety n X, V.carrier = (B : Set X) ∧ V.dim = d := by
    intro B
    obtain ⟨c,⟨k,hc⟩,hB⟩ := B.property
    have hkd : k = d := regular_dimension_of_dense_pure W hPure hc
    subst k
    let V : ClosedIrreducibleAnalyticSubvariety n X :=
      ⟨closure (component (n := n) W c),isClosed_closure,
        isComplexAnalyticallyIrreducible_closure_component hW hc,d,Nat.le_of_lt hd,
        ⟨c,regularAtDim_closure_component hc (mem_component_self hc)⟩⟩
    exact ⟨V,hB.symm,rfl⟩
  choose V hCarrier hDim using hEach
  refine ⟨V,hCarrier,hDim,?_,?_,?_⟩
  · simpa only [hCarrier] using locallyFinite_globalComponents hW
  · intro i j hij hsub
    apply hij
    exact global_components_incomparable W i j (by simpa only [hCarrier] using hsub)
  · rw [show (⋃ i, (V i).carrier) = ⋃₀ globalComponents (n := n) W by
      ext x
      simp only [mem_iUnion,mem_sUnion]
      constructor
      · rintro ⟨i,hi⟩
        exact ⟨i.1,i.2,by simpa only [hCarrier] using hi⟩
      · rintro ⟨B,hB,hx⟩
        exact ⟨⟨B,hB⟩,by simpa only [hCarrier] using hx⟩]
    exact sUnion_globalComponents hW
end
end Hironaka.HironakaG3PureGlobalComponents
