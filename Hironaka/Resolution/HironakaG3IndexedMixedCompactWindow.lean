import Hironaka.Resolution.HironakaG3IndexedMixedGluing
import Hironaka.Resolution.HironakaG3RChartOfMember
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedCompactWindow
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaBaseChange
  HironakaG3IndexedMixedWindowProducer HironakaActualLocallyFiniteBoundary
  HironakaG3IndexedMixedGluing HironakaG3RTowerClass HironakaG3RChartOfMember

/-- Every relatively compact ambient window admits a mixed-separation tower. -/
theorem indexed_mixed_over_compact_window {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      indexedMixedClass V D U Y T := by
  let s := (hV.finite_nonempty_inter_compact hK).toFinset
  let r := (hD.1.finite_nonempty_inter_compact hK).toFinset
  have hs : ∀ i, ((V i).carrier ∩ (U : Set X)).Nonempty → i ∈ s := by
    intro i ⟨z,hz,hzU⟩
    apply (hV.finite_nonempty_inter_compact hK).mem_toFinset.mpr
    exact ⟨z,hz,hUK hzU⟩
  have hr : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ r := by
    intro i ⟨z,hz,hzU⟩
    apply (hD.1.finite_nonempty_inter_compact hK).mem_toFinset.mpr
    exact ⟨z,hz,hUK hzU⟩
  have hRange : range (Subtype.val : U → X) ⊆ K := by
    rintro _ ⟨z,rfl⟩
    exact hUK z.property
  obtain ⟨Y,T,Ef,hTree,hOver,hAdm,hSNC,hDis⟩ :=
    sorted_window_producer (B₀ := CMfd.of (n := n) U) V hDim hDistinct D hD s r
      (Subtype.val : U → X) (isOpenHoloEmbedding_val (n := n) U) ⟨K,hK,hRange⟩
  exact ⟨Y,T,s,r,Ef,hs,hr,hTree,hOver,hAdm,hSNC,hDis⟩
/-- Every relatively compact ambient window is an actual mixed-separation
chart of a map glued from the indexed class. -/
theorem indexed_mixed_chart_over_compact_window {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    {P : Z → X} (hG : IsGluedFrom (indexedMixedClass V D) Z P)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ c : TowerChart (indexedMixedClass V D) Z P, c.U = U := by
  obtain ⟨Y,T,hT⟩ := indexed_mixed_over_compact_window V hV hDim hDistinct D hD U K hK hUK
  exact ⟨chartOfMember (indexed_mixed_comparisons V hDim hDistinct D) T hT
    hG.2.2.2 hG.1.continuous,rfl⟩

end
end Hironaka.HironakaG3IndexedMixedCompactWindow
