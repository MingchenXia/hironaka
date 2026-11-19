import Hironaka.Resolution.HironakaG3FiniteVisibleAtlas
import Hironaka.Resolution.HironakaG3RChartOfMember
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointVisibleMemberChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3RChartOfMember
  RestrictEmptyTower

/-- An actual compact-enclosed member of a disjoint component class becomes
an actual finite-visible chart of the same already-glued map. -/
theorem disjoint_visible_chart_of_member {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) (D : κ → Set X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (hD : LocallyFinite D) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (i : ι) (U : Opens X) (hUW : U ≤ W i) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L)
    (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y) (hT : K i U Y T) :
    ∃ c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P,
      c.U = U ∧ K i c.U c.Y c.T := by
  let R := (hD.finite_nonempty_inter_compact hL).toFinset
  have hVis : ∀ j, (D j ∩ (U : Set X)).Nonempty → j ∈ R := by
    intro j ⟨x,hxD,hxU⟩
    apply (hD.finite_nonempty_inter_compact hL).mem_toFinset.mpr
    exact ⟨x,hxD,hUL hxU⟩
  have hmem : finiteVisibleClass (disjointWindowClass A W K) D U Y T :=
    ⟨Or.inl ⟨i,hUW,hT⟩,R,hVis⟩
  have hCmp := finite_visible_comparisons _ D (disjoint_window_comparisons A W K hWindow hCompare hCentres)
  let c := chartOfMember hCmp T hmem hG.2.2.2 hG.1.continuous
  exact ⟨c,rfl,hT⟩
end
end Hironaka.HironakaG3DisjointVisibleMemberChart
