import Hironaka.Resolution.HironakaG3DisjointVisibleMemberChart
import Hironaka.Resolution.HironakaG3ComponentChartChain
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointComponentChartChain
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3DisjointVisibleMemberChart HironakaG3ComponentChartChain RestrictEmptyTower

/-- Compact-window members of one actual component class yield an actual
same-map nested finite-visible chart exhaustion of that component's window. -/
theorem disjoint_component_chart_chain {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) (D : κ → Set X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (hD : LocallyFinite D) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (i : ι)
    (hCompact : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) :
    ∃ c : ℕ → TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P,
      (∀ k, K i (c k).U (c k).Y (c k).T) ∧ (∀ k, (c k).U ≤ W i) ∧
      (∀ j k, j ≤ k → ((c j).V : Set Z) ⊆ (c k).V) ∧
      (⋃ k, ((c k).V : Set Z)) = P ⁻¹' (W i : Set X) := by
  apply component_chart_chain (W i)
  intro U hUW L hL hUL
  obtain ⟨Y,T,hT⟩ := hCompact U L hL hUL
  exact disjoint_visible_chart_of_member A W K D hWindow hCompare hCentres hD hG i U hUW L hL hUL Y T hT
end
end Hironaka.HironakaG3DisjointComponentChartChain
