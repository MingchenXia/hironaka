import Hironaka.Resolution.HironakaG3DisjointVisibleMemberChart
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointVisibleComplementChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3RChartOfMember
  RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

theorem disjoint_visible_complement_chart {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*}
    (C : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) (D : κ → Set X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    (hD : LocallyFinite D) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (U : Opens X) (hAvoid : (U : Set X) ⊆ (⋃ i, C i)ᶜ)
    (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    ∃ c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P,
      c.U = U ∧ IsEmptyTower c.T := by
  let T : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U) := .refl
  have hMem : finiteVisibleClass (disjointWindowClass C W K) D U (CMfd.of (n := n) U) T :=
    ⟨Or.inr ⟨hAvoid,trivial⟩,finite_visible_window D hD U L hL hUL⟩
  have hCmp := finite_visible_comparisons _ D (disjoint_window_comparisons C W K hWindow hCompare hCentres)
  let c := chartOfMember hCmp T hMem hG.2.2.2 hG.1.continuous
  exact ⟨c,rfl,trivial⟩
end
end Hironaka.HironakaG3DisjointVisibleComplementChart
